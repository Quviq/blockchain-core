-module(stake_txns_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-include_lib("stdlib/include/assert.hrl").

-include_lib("blockchain/include/blockchain_vars.hrl").
-include_lib("blockchain/include/blockchain.hrl").

-compile([export_all, nowarn_export_all]).

-behaviour(eqc_statem).

%% -- State and state functions ----------------------------------------------

%-record

-record(s,
        {
         init = false,
         chain,
         pending_validators = [],
         validators = [],
         a_validators = [],   %% [{nat(), #validator{}}] valid validators for account N
         unstaked_validators = [],
         group,
         account_addrs,
         chain_accounts,

         accounts,
         height = 1,
         pending_txns = #{},
         prepending_unstake = #{},
         pretransfer = [],
         pending_unstake = #{},
         txn_ctr = 1,
         txs = []   %% abstract transactions to be submitted for next block
        }).

-define(call(Fun, ArgList),
        {call, ?M, Fun, ArgList}).

-record(validator,
        {
         owner,
         addr,
         status,
         stake,
         sig_fun
        }).

-record(account,
        {
         id,
         address,
         balance,
         sig_fun,
         pub,
         priv
        }).

-define(M, ?MODULE).
-define(num_accounts, 5).
-define(initial_validators, 4).
-define(min_stake, ?bones(10000)).
-define(initial_balance, ?min_stake * 2).

-define(val, blockchain_ledger_validator_v1).

%% @doc Returns the state in which each test case starts. (Unless a different
%%      initial state is supplied explicitly to, e.g. commands/2.)
%%
%% In the future we want to derive the initial state for testing from now
%% hard coded values for total number of initial accounts and initial group size.
%% We parameterize this to allow future changes.
-spec initial_state() -> eqc_statem:symbolic_state().
initial_state() ->
    AccountIds = lists:seq(1, ?num_accounts),  %% account zero is GenOwner
    initial_state(AccountIds).

initial_state(AccountIds) ->
    #s{init = false,
       accounts = %% abstract, but not symbolic
           maps:from_list(
             lists:zip(AccountIds,
                       lists:duplicate(length(AccountIds),
                                       {?initial_balance, ?initial_balance})))
      }.

init_chain_env() ->
    %% these should be idempotent
    _ = application:ensure_all_started(lager),
    _ = blockchain_lock:start_link(),
    application:set_env(blockchain, test_mode, true),

    %% create a chain
    BaseDir = make_base_dir(),

    {no_genesis, Chain} = blockchain:new(BaseDir, "", undefined, undefined),

    {InitialVars, _MasterKeys} = blockchain_ct_utils:create_vars(val_vars()),

    GenesisMembers =
        [#validator{owner = 0,
                    addr = Addr,
                    sig_fun = SigFun,
                    stake = ?min_stake}
         || {Addr, {_Pub, _Priv, SigFun}} <- test_utils:generate_keys(?initial_validators)],

    Balance = ?initial_balance,
    [GenOwner |
     Accounts] = [#account{id = ID,
                           address = Addr,
                           %% give all accounts 1 val stake
                           balance = Balance,
                           sig_fun = SigFun,
                           pub = Pub,
                           priv = Priv}
                  || {ID, {Addr, {Pub, Priv, SigFun}}} <- lists:zip(lists:seq(0, ?num_accounts),
                                                                    test_utils:generate_keys(?num_accounts + 1))],

    GenPaymentTxs = [blockchain_txn_coinbase_v1:new(Addr, Balance)
                     || #account{address = Addr} <- Accounts],

    Addresses = [Addr || #validator{addr = Addr} <- GenesisMembers],

    InitialConsensusTxn =
        [blockchain_txn_gen_validator_v1:new(Addr, GenOwner#account.address, ?min_stake)
         || Addr <- Addresses],

    GenConsensusGroupTx = blockchain_txn_consensus_group_v1:new(
                            Addresses, <<"proof">>, 1, 0),
    Txs = InitialVars ++
        GenPaymentTxs ++
        InitialConsensusTxn ++
        [GenConsensusGroupTx],

    GenesisBlock = blockchain_block:new_genesis_block(Txs),
    ok = blockchain:integrate_genesis(GenesisBlock, Chain),

    ?assertEqual({ok, 1}, blockchain:height(Chain)),

    [{chain, Chain},
     {base_dir, BaseDir},
     {accounts, maps:from_list([{ID, Acct} || #account{id = ID} = Acct <- Accounts])},
     {validators, maps:from_list([{Addr, V} || #validator{addr = Addr} = V <- GenesisMembers])},
     {group, Addresses}].

make_base_dir() ->
    "stake-txns-dir-"++integer_to_list(rand:uniform(8999999) + 1000000).

val_vars() ->
    #{
      ?election_version => 5,
      ?validator_version => 2,
      ?validator_minimum_stake => ?min_stake,
      ?validator_liveness_grace_period => 100,
      ?validator_liveness_interval => 2000,
      ?stake_withdrawal_cooldown => 5,
      ?stake_withdrawal_max => 500,
      %?tenure_penalty => 1.0,
      ?dkg_penalty => 1.0,
      ?num_consensus_members => 4,
      ?election_bba_penalty => 0.5,
      ?election_seen_penalty => 0.5,
      ?tenure_penalty => 0.5,
      ?validator_penalty_filter => 1.0,
      ?penalty_history_limit => 100,
      ?election_interval => 3
     }.

%% -- Generators -------------------------------------------------------------

weight(_S, init) ->
    1;
weight(S, validator) ->
    50 - length(S#s.a_validators);
weight(_S, transfer) ->
    50;
weight(_S, stake) ->
    30;
weight(_S, unstake) ->
    30;
weight(S, election) ->
    Interval = maps:get(?election_interval, val_vars()),
    %% Make it likely to pick election command at height that election may take place
    if S#s.height rem Interval == 0 -> 100;
       true -> 10
    end;
weight(S, block) ->
    Interval = maps:get(?election_interval, val_vars()),
    %% Favour election over block at height that election may take place
    if S#s.height rem Interval -> 10;
       true -> 100
    end.

command_precondition_common(S, Cmd) ->
    S#s.init /= false orelse Cmd == init.

invariant(#s{chain = undefined}) ->
    true;  %% when chain is not yet initialized
invariant(#s{chain = Chain,
             validators = Vals,
             pending_unstake = Pends,
             accounts = Accounts,
             account_addrs = Addrs
            }) ->
    Ledger = blockchain:ledger(Chain),
    Circ = blockchain_ledger_v1:query_circulating_hnt(Ledger),
    Cool = blockchain_ledger_v1:query_cooldown_hnt(Ledger),
    Staked = blockchain_ledger_v1:query_staked_hnt(Ledger),
    LedgerVals0 = blockchain_ledger_v1:snapshot_validators(Ledger),
    LedgerVals =
        lists:map(fun({Addr, BinVal}) ->
                          {Addr, blockchain_ledger_validator_v1:deserialize(BinVal)}
                  end, LedgerVals0),

    Stake = ?min_stake,

    NumPends = length(lists:flatten(maps:values(Pends))),
    NumVals = maps:size(Vals),
    lager:debug("circ ~p cool ~p staked ~p vals ~p pend ~p",
                [Circ, Cool, Staked, NumVals, NumPends]),

    try
        %% check that the ledger amounts match the expected state from the model
        ExpCool = NumPends * Stake,
        case ExpCool == Cool of
            false -> throw({cool, ExpCool, Cool, Pends});
            _ -> ok
        end,
        ExpStaked = NumVals * Stake,
        case ExpStaked == Staked of
            false -> throw({staked, ExpStaked, Staked, Vals});
            _ -> ok
        end,
        ExpCirc = (?num_accounts * 2 - (NumVals - ?initial_validators) - NumPends) * Stake,
        case ExpCirc == Circ of
            false -> throw({circ, ExpCirc, Circ});
            _ -> ok
        end,

        %% make sure that all balances are correct
        ExpBals0 =
            lists:foldl(
              fun({_Addr, V}, Acc) ->
                      StakeAmt = ?val:stake(V),
                      Owner = ?val:owner_address(V),
                      %% we have 4 initial validators not owned by modeled accounts who we don't
                      %% care about from a balance perspective
                      case maps:find(Owner, Acc) of
                          {ok, {Bal, Tot}} ->
                              case ?val:status(V) of
                                  staked ->
                                      Acc#{Owner => {Bal, Tot + StakeAmt}};
                                  unstaked ->
                                      Acc;
                                  cooldown ->
                                      Acc#{Owner => {Bal, Tot + StakeAmt}}
                              end;
                          _ -> Acc
                      end
              end,
              maps:from_list([begin
                                  {ok, Ent} = blockchain_ledger_v1:find_entry(Addr, Ledger),
                                  Bal = blockchain_ledger_entry_v1:balance(Ent),
                                  {Addr, {Bal, Bal}}
                              end || Addr <- maps:keys(Addrs)]),
              LedgerVals),
        ExpBals =
            maps:fold(fun(Addr, BalTot, Acc) ->
                              case maps:find(Addr, Addrs) of
                                  {ok, ID} ->
                                      Acc#{ID => BalTot};
                                  _ -> Acc
                              end
                      end, #{}, ExpBals0),
        case ExpBals == Accounts of
            true ->
                ok;
            false ->
                throw({balance_issue, ExpBals, Accounts})
        end,
        true
    catch throw:E ->
            E
    end.

add_pending(Txn, ID, Pending, Reason) ->
    Pending#{ID => {Reason, Txn}}.


update_pending({ok, Valid, Invalid0, _Block}, Pending) ->
    {Invalid, _Reasons} = lists:unzip(Invalid0),
    ToRemove = Valid ++ Invalid,
    maps:filter(
      fun(_ID, {_tag, Txn}) ->
              not lists:member(Txn, ToRemove)
      end, Pending).

%% -- Give commands access to reading the state at runtime -------------------

wrap_call(S, {call, Mod, Cmd, Args}) when
      Cmd == stake; Cmd == unstake ->
    try {ok, apply(Mod, Cmd, [S | Args])}
    catch
        _:Reason:ST -> {error, {'EXIT', {Reason, ST}}, []}
    end;
wrap_call(_S, {call, Mod, Cmd, Args}) ->
    try  {ok, apply(Mod, Cmd, Args)}
    catch
        _:Reason:ST -> {error, {'EXIT', {Reason, ST}}, []}
    end.

%% -- Commands ---------------------------------------------------------------
init_pre(S, _) ->
    S#s.init == false.

init_args(_S) ->
    [].

%% This will generate a new state in which environment variables are
%% used inside symbolic calls. The invariant and post condition see the
%% dynamic values
init() ->
    ok.

init_next(S, _, []) ->
    S#s{init = true,
        chain = {var, chain},
        group = {var, group},
        validators = {var, validators},
        chain_accounts = {var, accounts},
        account_addrs = {call, ?M, init_accts, [{var, accounts}]}}.

init_accts(Accounts) ->
    maps:fold(fun(ID, #account{address = Addr}, Acc) ->
                      Acc#{Addr => ID}
              end, #{}, Accounts).

%% --- Operation: validator ---
%% create a new VALID validator and add symbolic representation to state

validator_args(_S) ->
    [choose(1, ?num_accounts)].

validator(Account) ->
    [{Address, {_, _, Sig}}] = test_utils:generate_keys(1),
    #validator{owner = Account,
               addr = Address,
               sig_fun = Sig,
               stake = ?min_stake}.

%% The symbolic variable ensures that we later use the right validator for the intended validation
validator_next(S, V, [Account]) ->
    S#s{a_validators = S#s.a_validators ++ [{Account, V}]}.


%% stake command ---------------------------------------------
stake_dynamicpre(#s{unstaked_validators = Dead0}, [_, _, bad_validator]) ->
    Dead = lists:flatten(Dead0),
    Dead /= [];
stake_dynamicpre(S, [Account, _Dead, balance]) ->
    lists:member(Account, maps:keys(maps:filter(fun lt_stake/2, S#s.accounts)));
%% we need at least one possible staker for these others to be reasonable
stake_dynamicpre(S, [Account, _Dead, _]) ->
    lists:member(Account, maps:keys(maps:filter(fun ge_stake/2, S#s.accounts))).

stake_pre(S) ->
    S#s.a_validators /= [].

%% Given the reason, other parts can be selected easier
stake_args(S) ->
    ?LET(Reason, fault(oneof([balance, bad_sig, bad_owner] ++
                                 [{bad_validator, V} || V <- S#s.unstaked_validators]), valid),
    ?LET({Account, Validator}, elements(S#s.a_validators),
         case Reason of
             {bad_validator, Dead} ->
                 [Account, Dead, bad_validator];
             _ ->
                 [Account, Validator, Reason]
         end)).


stake(S, Account, Validator,  Reason) ->
    lager:info("val ~p acct ~p reason ~p", [Validator, Account, Reason]),
    {AccountAddress, SigFun} = fault_inject(S, Account, Reason),
    stake_txn(Validator#validator.addr, AccountAddress, SigFun).

stake_txn(Val, AccountAddress, SigFun) ->
    Txn = blockchain_txn_stake_validator_v1:new(
            Val, AccountAddress,
            ?min_stake,
            35000
           ),
    blockchain_txn_stake_validator_v1:sign(Txn, SigFun).

%% todo: try with mainnet/testnet keys
stake_next(#s{} = S,
           V,
           [Account, Validator, Reason]) ->
    S#s{%% accounts = ?call(update_accounts, [stake, SymAccounts, Reason, V]),
        pending_txns = ?call(add_pending, [V, S#s.txn_ctr, S#s.pending_txns, Reason]),
        pending_validators = S#s.pending_validators ++ [Validator || Reason == valid],
        txs = S#s.txs ++ [{Reason, stake,  [Account]}],
        txn_ctr = S#s.txn_ctr + 1}.

%% update_validators({ok, Val, _Txn}) -> Val.

%% unstake command ---------------------------------------------
unstake_dynamicpre(S,
                   [_, _, _, bad_validator]) ->
    lists:flatten(S#s.unstaked_validators) /= [];
unstake_dynamicpre(#s{pretransfer = Pretransfer0,
                      prepending_unstake = Unstaked,
                      group = Group0,
                      validators = Validators0},
                   [_, _, _, in_group]) ->
    Group = selectable_group_vals(Group0, Validators0),
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    Group =/= []
        andalso (Validators -- (Pretransfer ++ lists:flatten(maps:values(Unstaked)))) /= [];
unstake_dynamicpre(#s{pretransfer = Pretransfer0,
                      prepending_unstake = Unstaked,
                      group = Group0,
                      validators = Validators0},
                   [_, _, _, _Reason]) ->
    Group = selectable_group_vals(Group0, Validators0),
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    (Validators -- (Group ++ Pretransfer ++ lists:flatten(maps:values(Unstaked)))) /= [].

no_id0(_, #validator{owner = 0}) ->
    false;
no_id0(_, _) ->
    true.

unstake_pre(S) ->
    S#s.a_validators /= [].

unstake_args(S) ->
    ?LET({Account, Validator}, elements(S#s.a_validators),
    ?LET(Reason, fault(elements([bad_account, bad_sig,
                                 {wrong_account, ?SUCHTHAT(N, choose(1,10), N /= Account)}, in_group] ++
                                    [{bad_validator, V} || V <- S#s.unstaked_validators]), valid),

         [Account,
          case Reason of
              in_group ->  %% probably this is the valid one?
                  ?LET(N, choose(1,4),
                       {call, maps, get, [{call, lists, nth, [N, S#s.group]}, S#s.validators]});   %% fix this later
              {bad_validator, Dead} -> Dead;
              _ ->
                  Validator  %% by construction owner is not 0
           end,
          6,  %% unstakeheight
          Reason])).

unstake(S, Account, Validator, UnstakeHeight, Reason) ->
    Height = S#s.height,
    %% {_Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    %% Val = case Reason of
    %%           bad_validator -> Dead;
    %%           in_group -> select(Group);
    %%           _ -> select(maps:values(maps:filter(fun no_id0/2, SymVals))
    %%                       -- (Group ++ Pretransfer ++ lists:flatten(maps:values(Unstaked))))
    %%       end,
    lager:info("unstake ~p reas ~p", [Validator, Reason]),
    {AccountAddress, SigFun} = fault_inject(S, Account, Reason),
    unstake_txn(Validator#validator.addr, AccountAddress, SigFun, Height, UnstakeHeight, Reason).

unstake_txn(Val, AccountAddress, SigFun, Height, UnstakeHeight, Reason) ->
    Txn = blockchain_txn_unstake_validator_v1:new(
            Val, AccountAddress,
            ?min_stake,
            Height + UnstakeHeight,
            35000
           ),
    STxn = blockchain_txn_unstake_validator_v1:sign(Txn, SigFun),
    case Reason of
        bad_sig ->
            blockchain_txn_unstake_validator_v1:owner_signature(<<0:512>>, Txn);
        _ ->
            STxn
    end.

unstake_next(S, V, [Account, Validator, UnstakeHeight, Reason]) ->
    S#s{prepending_unstake =
            if Reason == valid ->
                    ?call(update_preunstake, [S#s.prepending_unstake, Validator, S#s.height + UnstakeHeight]);
               true -> S#s.prepending_unstake
            end,
        pending_txns = ?call(add_pending, [V, S#s.txn_ctr, S#s.pending_txns, Reason]),
        txs = S#s.txs ++ [{Reason, unstake,  [Account]}],
        txn_ctr = S#s.txn_ctr + 1}.

update_preunstake(Pending, Val, UnstakeHeight) ->
    maps:update_with(UnstakeHeight, fun(X) -> [Val | X] end, [Val], Pending).

unstake_post(S, [_Account, _Validator, UnstakeHeight, Reason], Txn) ->
    case Reason of
        valid ->
            eq(blockchain_txn_unstake_validator_v1:stake_release_height(Txn), S#s.height + UnstakeHeight);
        _ ->
            true
    end.

%%%%
%%% transfer command ---------------------------------------------
%%%%

transfer_dynamicpre(#s{pretransfer = Pretransfer0,
                       group = Group,
                       accounts = Accounts,
                       prepending_unstake = Unstaked,
                       validators = Validators0}, [_, _, _, _, _, _, InAddr, in_group]) ->
    Amt = case InAddr of
              true -> 0;
              false -> 0;
              amount -> ?bones(9000)
          end,
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    Possible = (Validators -- (Pretransfer ++ lists:flatten(maps:values(Unstaked)))),
    PossibleAddrs = [Addr || #validator{addr = Addr} <- Possible],
    Possible /= []
        andalso lists:any(fun(X) -> lists:member(X, Group) end, PossibleAddrs)
        andalso maps:size(maps:filter(fun(_, {Bal, _Tot}) -> Bal >= Amt end, Accounts)) =/= 0;
transfer_dynamicpre(#s{pretransfer = Pretransfer0,
                       accounts = Accounts,
                       prepending_unstake = Unstaked,
                       validators = Validators0,
                       unstaked_validators = Dead0}, [_, _, _, _, _, _, InAddr, bad_validator]) ->
    Dead = lists:flatten(Dead0),
    Amt = case InAddr of
              true -> 0;
              false -> 0;
              amount -> ?bones(9000)
          end,
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    (Validators -- (Pretransfer ++ lists:flatten(maps:values(Unstaked)))) /= []
        andalso maps:size(maps:filter(fun(_, {Bal, _Tot}) -> Bal >= Amt end, Accounts)) =/= 0
        andalso Dead /= [];
transfer_dynamicpre(#s{pretransfer = Pretransfer0,
                       group = Group0,
                       accounts = Accounts,
                       prepending_unstake = Unstaked,
                       validators = Validators0}, [_, _, _, _, _, _, amount, valid]) ->
    %% when amount + valid, we need to make sure that there is something it's possible to transfer
    Group = selectable_group_vals(Group0, Validators0),
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    (Validators -- (Group ++ Pretransfer ++ lists:flatten(maps:values(Unstaked)))) /= []
        andalso
        %% and that there is an account with enough balance to cover the amount
        maps:size(maps:filter(fun(_, {Bal, _Tot}) -> Bal > ?bones(9000) end, Accounts)) =/= 0;
transfer_dynamicpre(#s{pretransfer = Pretransfer0,
                       group = Group0,
                       prepending_unstake = Unstaked,
                       validators = Validators0}, _Args) ->
    Group = selectable_group_vals(Group0, Validators0),
    Validators = maps:values(maps:filter(fun no_id0/2, Validators0)),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    (Validators -- (Group ++ Pretransfer ++ lists:flatten(maps:values(Unstaked)))) /= [].

acct_transfer() ->
    oneof([true, false, amount]).

transfer_args(S) ->
    oneof([
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), valid],
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), bad_sig],
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), bad_account],
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), wrong_account],
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), in_group],
           [{var, accounts}, S#s.group, S#s.prepending_unstake, S#s.pretransfer,
            S#s.validators, S#s.unstaked_validators, acct_transfer(), bad_validator]
          ]).

transfer(Accounts, Group0, Unstaked, Pretransfer0, SymVals, Dead, IntraAddr, Reason) ->
    lager:info("xxx ~p",[Pretransfer0]),
    Group = selectable_group_vals(Group0, SymVals),
    {Pretransfer, _Amts, _NewVals} = lists:unzip3(Pretransfer0),
    OldVal = case Reason of
                 bad_validator -> select(Dead);
                 in_group -> select(Group);
                 _ -> select(maps:values(maps:filter(fun no_id0/2, SymVals))
                             -- (Pretransfer ++ lists:flatten(maps:values(Unstaked))))
             end,
    [{Address, {_, _, Sig}}] = test_utils:generate_keys(1),
    {Txn, Amt, NewVal} = transfer_txn(OldVal, Address, Sig, IntraAddr, Accounts, Reason),
    {OldVal, NewVal, Amt, Txn}.

transfer_next(#s{} = S,
              V,
              [_Accounts, _Group, _Vals, _, _, _, _IntraAddr, Reason]) ->
    S#s{pretransfer = ?call(update_pretransfer, [S#s.pretransfer, Reason, V]),
        pending_txns = ?call(add_trans_pending, [V, S#s.txn_ctr, S#s.pending_txns, Reason]),
        %% pending_validators = ?call(transfer_update_validators, [S#s.pending_validators, Reason, V]),
        txn_ctr = S#s.txn_ctr + 1}.

add_trans_pending({_Old, _New, _Amt, Txn}, ID, Pending, Reason) ->
    Pending#{ID => {Reason, Txn}}.

update_pretransfer(Pretransfer, valid, {Val, NewVal, Amt, _Txn}) ->
    [{Val, Amt, NewVal} | Pretransfer];
update_pretransfer(Pretransfer, _Reason, _Res) ->
    Pretransfer.

transfer_txn(#validator{owner = Owner, addr = Addr},
             NewValAddr, NewValSig,
             IntraAddr,
             Accounts,
             Reason) ->
    %% can't do bad_account because that will just create a new account
    Account =
        case Reason of
            %% make up a non-existent account
            bad_account ->
                [{Acct, {_, _, Sig}}] = test_utils:generate_keys(1),
                #account{address = Acct, sig_fun = Sig};
            %% use existing but non-owner account
            wrong_account ->
                element(2, hd(maps:to_list(maps:remove(Owner, Accounts))));
            _ ->
                maps:get(Owner, Accounts)
        end,

    {{ID, NewAccount}, Amt} =
        case IntraAddr of
            false -> {{Account#account.id, #account{address = <<>>}}, 0};
            true -> {select(maps:to_list(maps:remove(Owner, Accounts))), 0};
            amount -> {select(maps:to_list(maps:remove(Owner, Accounts))), ?bones(9000)}
        end,

    NewVal = #validator{owner = ID,
                        addr = NewValAddr,
                        sig_fun = NewValSig,
                        stake = ?min_stake},

    Txn = blockchain_txn_transfer_validator_stake_v1:new(
            Addr, NewValAddr,
            Account#account.address,
            NewAccount#account.address,
            ?min_stake,
            Amt,
            35000
           ),
    STxn0 = blockchain_txn_transfer_validator_stake_v1:sign(Txn, Account#account.sig_fun),
    STxn = case IntraAddr of
               OK when OK == true; OK == amount ->
                   blockchain_txn_transfer_validator_stake_v1:new_owner_sign(
                     STxn0,
                     NewAccount#account.sig_fun);
               false -> STxn0
           end,
    FinalTxn =
        case Reason of
            bad_sig ->
                blockchain_txn_transfer_validator_stake_v1:old_owner_signature(<<0:512>>, Txn);
            _ ->
                STxn
        end,
    {FinalTxn, Amt, NewVal}.

%% election psuedo-commands ---------------------------------------------
election_pre(S, _) ->
    S#s.height rem 3 == 0.

election_args(S) ->
    [S#s.height, S#s.chain, S#s.validators, S#s.group].

election(Height, Chain, Validators, CurrGroup)  ->
    Ledger = blockchain:ledger(Chain),
    {ok, Block} = blockchain:get_block(Height, Chain),
    Hash = blockchain_block:hash_block(Block),
    NewGroup = blockchain_election:new_group(Ledger, Hash, 4, 0),
    lager:info("groups ~p -> ~p",
               [lists:map(fun blockchain_utils:addr2name/1, CurrGroup),
                lists:map(fun blockchain_utils:addr2name/1, NewGroup)]),

    Artifact = term_to_binary(NewGroup),

    Signatures = signatures(NewGroup, Validators, Artifact),
    Proof = term_to_binary(Signatures, [compressed]),

    GroupTxn = blockchain_txn_consensus_group_v1:new(
                 NewGroup, Proof, Height, 0),

    {ok, _Valid, _Invalid, NewBlock} = block(Chain, CurrGroup, Validators, #{whatever => {valid, GroupTxn}}),
    %% indirect call to model function block adds block to chain
    {NewGroup, NewBlock}.

election_next(#s{pending_txns = PendTxns} = S, V, _Args) ->
    NewHeight = S#s.height + 1,
    Update = ?call(fixup_txns, [S#s.group, V, PendTxns,
                                S#s.prepending_unstake, S#s.pretransfer]),
    S#s{group = ?call(update_group, [V]),
        pretransfer = {call, erlang, element, [3, Update]},
        prepending_unstake = {call, erlang, element, [2, Update]},
        pending_txns = {call, erlang, element, [1, Update]},
        height = NewHeight}.

update_group({NewGroup, _Block}) ->
    NewGroup.

fixup_txns(OldGroup, {NewGroup, _}, Pending, Unstake, Pretransfer) ->
    maps:fold(
      fun(K, {Reason, Txn} = Orig, {Acc, Uns, Pre}) ->
              case blockchain_txn:type(Txn) of
                  blockchain_txn_transfer_validator_stake_v1 ->
                      OldVal = blockchain_txn_transfer_validator_stake_v1:old_validator(Txn),
                      case Reason of
                          in_group ->
                              %% if this is an invalid txn but an election happens, it becomes valid
                              %% if the validator was elected out
                              case lists:member(OldVal, OldGroup) andalso
                                  not lists:member(OldVal, NewGroup) of
                                  true ->
                                      %% this becomes valid, but for now the new val is lost?
                                      %%Pre1 = [{OldV, Amt, NewV} | Pre],
                                      %%{Acc#{K => {valid, Txn}}, Uns, Pre1};
                                      {Acc, Uns, Pre};
                                  _ ->
                                      {Acc#{K => Orig}, Uns, Pre}
                              end;
                          valid ->
                              case lists:member(OldVal, NewGroup) of
                                  true ->
                                      %% this becomes invalid, so needs to be removed from pretransfer
                                      Pre1 = lists:filter(fun({#validator{addr = Addr}, _, _}) ->
                                                                  Addr /= OldVal
                                                          end, Pre),
                                      {Acc#{K => {in_group, Txn}}, Uns, Pre1};
                                  _ ->
                                      {Acc#{K => Orig}, Uns, Pre}
                              end;
                          _ -> {Acc#{K => Orig}, Uns, Pre}
                      end;
                  blockchain_txn_unstake_validator_v1 ->
                      OldVal = blockchain_txn_unstake_validator_v1:address(Txn),
                      case Reason of
                          in_group ->
                              %% if this is an invalid txn but an election happens, it becomes valid
                              %% if the validator was elected out
                              case lists:member(OldVal, OldGroup) andalso
                                  not lists:member(OldVal, NewGroup) of
                                  true ->
                                      %% this becomes valid, so needs to be added to prepending
                                      %% unstake, but the height is lost, so we drop it?
                                      %% {valid, Txn};
                                      {Acc, Uns, Pre};
                                  _ ->
                                      {Acc#{K => Orig}, Uns, Pre}
                             end;
                          valid ->
                              case lists:member(OldVal, NewGroup) of
                                  true ->
                                      %% this becomes invalid, so needs to be removed from unstake
                                      Uns1 = maps:map(fun(_Ht, Lst) ->
                                                              lists:filter(fun(#validator{addr = Addr}) ->
                                                                                   Addr /= OldVal
                                                                           end,
                                                                           Lst)
                                                      end, Uns),
                                      {Acc#{K => {in_group, Txn}}, Uns1, Pre};
                                  _ ->
                                      {Acc#{K => Orig}, Uns, Pre}
                              end;
                          _ -> {Acc#{K => Orig}, Uns, Pre}
                      end;
                  _ ->
                      {Acc#{K => Orig}, Uns, Pre}
              end
      end,
      {#{}, Unstake, Pretransfer},
      Pending).

%% block commands ---------------------------------------------


block_args(S) ->
    [S#s.chain, S#s.group, S#s.validators, S#s.pending_txns].

block(Chain, Group, Validators, Txns) ->
    STxns = lists:sort(fun blockchain_txn:sort/2, element(2, lists:unzip(maps:values(Txns)))),
    {Valid, Invalid} = blockchain_txn:validate(STxns, Chain),
    {ok, HeadBlock} = blockchain:head_block(Chain),
    {ok, PrevHash} = blockchain:head_hash(Chain),
    Height = blockchain_block:height(HeadBlock) + 1,
    Time = blockchain_block:time(HeadBlock) + 1,
    MBlock =
        #{prev_hash => PrevHash,
          height => Height,
          transactions => Valid,
          signatures => [],
          time => Time,
          hbbft_round => 0,
          election_epoch => 1,
          epoch_start => 0,
          seen_votes => [],
          bba_completion => <<>>
         },
    Block0 = blockchain_block_v1:new(MBlock),
    BinBlock = blockchain_block:serialize(Block0),
    Signatures = signatures(Group, Validators, BinBlock),
    Block1 = blockchain_block:set_signatures(Block0, Signatures),
    %% lager:info("txns ~p", [Block1]),
    ok = blockchain:add_block(Block1, Chain),
    {ok, Valid, Invalid, Block1}.

block_next(#s{} = S,
           V,
           [_Chain, _Group, _, _Transactions]) ->
    NewHeight = S#s.height + 1,
    S#s{height = NewHeight,

        accounts = ?call(block_update_accounts, [NewHeight, S#s.accounts,
                                                 S#s.pending_validators,
                                                 S#s.pretransfer,
                                                 S#s.pending_unstake]),

        pending_validators = [],
        validators = ?call(block_update_validators, [S#s.pending_validators,
                                                     S#s.prepending_unstake,
                                                     S#s.pretransfer,
                                                     S#s.validators]),

        pretransfer = [],
        prepending_unstake = #{},
        pending_unstake = ?call(update_unstake, [NewHeight, S#s.prepending_unstake, S#s.pending_unstake]),
        unstaked_validators = S#s.unstaked_validators ++
            lists:flatten([ ?call(update_dead_validators, [S#s.prepending_unstake])]),

        pending_txns = ?call(update_pending, [V, S#s.pending_txns])}.

block_update_validators(PV, Unstakes, Pretransfer0, V) ->
    {Pretransfer, _Amts, NewVals} = lists:unzip3(Pretransfer0),
    New = (PV ++ NewVals),
    V2 = lists:foldl(
           fun(Val = #validator{addr = Addr}, Acc) ->
                   Acc#{Addr => Val}
           end,
           V,
           New),
    lists:foldl(
      fun(#validator{addr = Addr}, Acc) ->
              maps:remove(Addr, Acc)
      end,
      V2,
      Pretransfer ++ lists:flatten(maps:values(Unstakes))).

update_dead_validators(Unstakes) ->
    lists:flatten(maps:values(Unstakes)).

update_unstake(Height, PP, P) ->
    maps:remove(Height, maps:merge(PP, P)).

block_update_accounts(Height, Accounts, PendingValidators, PendingTransfer, PendingUnstake) ->
    Accounts1 =
        case maps:find(Height, PendingUnstake) of
            {ok, Vals} ->
                lists:foldl(
                  fun(Val, Acc) ->
                          {Bal, Tot} = maps:get(Val#validator.owner, Acc),
                          Acc#{Val#validator.owner => {Bal + ?min_stake, Tot}}
                  end, Accounts,
                  Vals);
            _ -> Accounts
        end,
    Accounts2 =
        lists:foldl(
          fun(Val, Acc) ->
                  {Bal, Tot} = maps:get(Val#validator.owner, Acc),
                  Acc#{Val#validator.owner => {Bal - ?min_stake, Tot}}
          end, Accounts1,
          PendingValidators),
    lists:foldl(
      fun({OldVal, Amt, NewVal}, Acc) ->
              case OldVal#validator.owner == NewVal#validator.owner of
                  true ->
                      Acc; % no overall change
                  false ->
                      {OldBal, OldTot} = maps:get(OldVal#validator.owner, Acc),
                      {NewBal, NewTot} = maps:get(NewVal#validator.owner, Acc),
                      Acc#{OldVal#validator.owner => {OldBal + Amt, OldTot + Amt - ?min_stake},
                           NewVal#validator.owner => {NewBal - Amt, NewTot - Amt + ?min_stake}}
              end
      end,
      Accounts2,
      PendingTransfer).

block_post(#s{pending_txns = Pend,
              validators = _vals,
              accounts = _Accounts} = _S,
              _Args,
              {ok, Valid, Invalid0, _Block}) ->
    {Invalid, _Reasons} = lists:unzip(Invalid0),
    Ret =
        maps:fold(
          fun(_ID, {valid, Txn}, Acc) ->
                  %% we either need to be in the valid txns, or not in the invalid txns, i.e. not in the
                  %% list at all
                  case lists:member(Txn, Valid) orelse
                      not lists:member(Txn, Invalid) of
                      false ->
                          [{valid, Txn}];
                      _ -> Acc
                  end;
             %% all non-'valid' reason tags are invalid
             (__ID, {Reason, Txn}, Acc) ->
                  %% we either need to be in the valid txns, or not in the invalid txns, i.e. not in the
                  %% list at all
                  case lists:member(Txn, Invalid) orelse
                      not lists:member(Txn, Valid) of
                      false ->
                          [{Reason, Txn}];
                      _ -> Acc
                  end
          end,
          [],
          Pend),
    case Ret of
        [] -> true;
        _ -> Ret
    end.

%% -- Property ---------------------------------------------------------------
%% prop_stake() ->
%%     with_parameters(
%%       [{show_states, false},  % make true to print state at each transition
%%        {print_counterexample, true}],
prop_stake() ->
    fault_rate(1, 20,
    ?FORALL(
       %% default to longer commands sequences for better coverage
       Cmds, more_commands(25, commands(?M)),
       %% Cmds, noshrink(more_commands(5, commands(?M))),
       begin
           Env = init_chain_env(),
           {H, S, Res} = run_commands(Cmds, Env),
           measure(height, S#s.height,
           aggregate(command_names(Cmds),
           aggregate(with_title("abstract transactions"), S#s.txs,
           eqc_statem:pretty_commands(?M,
                                      Cmds,
                                      {H, S, Res},
                                      Env,
                                      cleanup(eqc_symbolic:eval(S), Env)
                                      andalso Res == ok))))
       end)).

%% @doc Run property repeatedly to find as many different bugs as
%% possible. Runs for 10 seconds before giving up finding more bugs.
-spec bugs() -> [eqc_statem:bug()].
bugs() -> bugs(10).

%% @doc Run property repeatedly to find as many different bugs as
%% possible. Runs for N seconds before giving up finding more bugs.
-spec bugs(non_neg_integer()) -> [eqc_statem:bug()].
bugs(N) -> bugs(N, []).

%% @doc Run property repeatedly to find as many different bugs as
%% possible. Takes testing time and already found bugs as arguments.
-spec bugs(non_neg_integer(), [eqc_statem:bug()]) -> [eqc_statem:bug()].
bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_stake()), 20, Bugs).

%%% helpers


%% THIS is a fat NO-No. No randomness other than by QuickCheck
%% If you do this, you cannot replay the same test and hence cannot shrink
select([]) ->
    error(zero_len_list);
select(Lst0) ->
    Lst = lists:flatten(Lst0),
    Len = length(Lst),
    lists:nth(rand:uniform(Len), Lst).

signatures(Members, Validators, Bin) ->
    lists:foldl(
      fun(Addr, Acc) ->
              #validator{sig_fun = F} = maps:get(Addr, Validators),
              Sig = F(Bin),
              [{Addr, Sig}|Acc]
      end, [], Members).

selectable_group_vals(Group, Vals0) ->
    Vals = maps:filter(fun no_id0/2, Vals0),
    lists:foldl(
      fun(Mem, Acc) ->
              case maps:find(Mem, Vals) of
                  {ok, V} -> [V | Acc];
                  _ -> Acc
              end
      end,
      [], Group).

lt_stake(_, Value) ->
    lt_stake(Value).

lt_stake({Bones, _}) ->
    Bones < ?min_stake.

ge_stake(_, Value) ->
    ge_stake(Value).

ge_stake({Bones, _}) ->
    Bones >= ?min_stake.

cleanup(#s{}, Env) ->
    Dir = maps:get(base_dir, maps:from_list(Env)),
    lager:info("entering cleanup"),
    PWD = string:trim(os:cmd("pwd")),
    os:cmd("rm -r " ++ PWD ++ "/" ++ Dir),
    true.

%% returns AccountAddress, SigFun with possible fault injected
fault_inject(S, Account, Reason) ->
    #account{address = Address,
             sig_fun = SigFun} = maps:get(Account, S#s.chain_accounts),
    [{WrongAddress, {_, _, WrongSigFun}}] = test_utils:generate_keys(1),
    case Reason of
        bad_owner -> {WrongAddress, SigFun};
        bad_sig -> {Address, WrongSigFun};
        bad_account -> {WrongAddress, WrongSigFun};
        {wrong_account, WA} ->
            #account{address = WAddress,
                     sig_fun = WSigFun} = maps:get(WA, S#s.chain_accounts),
            {WAddress, WSigFun};
        _ ->
            {Address, SigFun}
    end.
