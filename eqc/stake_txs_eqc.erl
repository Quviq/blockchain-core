%%
%% idea of this model
%%    create abstract transactions in the state, a kind of transaction pool
%%    Build a block of those transaction and verify that the valid transactions
%%       are accepted and invalid transactions are rejected
%%    Verification is done at the moment we add a block, not earlier
%%    There might be non-determinism, deal with that when it demonstrates itself

-module(stake_txs_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-include_lib("stdlib/include/assert.hrl").

-include_lib("blockchain/include/blockchain_vars.hrl").
-include_lib("blockchain/include/blockchain.hrl").

-compile([export_all, nowarn_export_all, nowarn_unused_record]).

-behaviour(eqc_statem).

%% -- State and state functions ----------------------------------------------

%-record

-record(s,
        {
         used_validators = [],   %% cannot be used again?
         group = [],   %% validators for those that have stake?
         staked = [],
         unstaked = [],
         transferred = [],

         accounts = [],   %% {index, balance, stake}
         height = 0,
         val_ctr = 0,
         txs = [],   %% abstract transactions to be submitted for next block
         chain,

         %% mapping from account to runtime account address and details
         %% Purposely using a list instead of a map
         validator_idxs = [],
         account_idxs = []
        }).

-define(call(Fun, ArgList),
        {call, ?M, Fun, ArgList}).

-record(validator,
        {
         owner,
         addr,
         sig_fun
        }).

-record(account,
        {
         id,
         address,
         sig_fun
        }).

-define(M, ?MODULE).
-define(num_accounts, 5).
-define(initial_validators, 4).  %% Not that this is also ?num_consensus_members
-define(min_stake, ?bones(10000)).
-define(initial_balance, ?min_stake * 2).

-define(val, blockchain_ledger_validator_v1).

initial_state() ->
    #s{accounts = []}.

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

%% -- Give commands access to reading the state at runtime -------------------

wrap_call(S, {call, Mod, Cmd, Args}) ->
    WithState = lists:member(Cmd, [genesis_txs, add_block,
                                   balances, staked,
                                   tx_transfer, tx_coinbase, tx_consensus, tx_stake]),
    try if WithState -> {ok, apply(Mod, Cmd, [S | Args])};
           not WithState -> {ok, apply(Mod, Cmd, Args)}
        end
    catch
        _:Reason:ST -> {error, {'EXIT', {Reason, ST}}, []}
    end.

%% -- Commands ---------------------------------------------------------------
init_chain_pre(S) ->
    S#s.chain == undefined.

init_chain_args(_S) ->
    [{var, basedir}].

%% Create a new empty chain and return a reference to it
init_chain(BaseDir) ->
    {no_genesis, Chain} = blockchain:new(BaseDir, "", undefined, undefined),
    Chain.

init_chain_next(S, V, [_]) ->
    S#s{chain = V}.

%% --- Operation: create_account ---

create_account_args(S) ->
    [length(S#s.account_idxs)].

create_account(Id) ->
    [{Addr, {_, _, SigFun}}] = test_utils:generate_keys(1),
    #account{id = Id,
             address = Addr,
             sig_fun = SigFun}.

create_account_next(S, V, [Id]) ->
    S#s{account_idxs = S#s.account_idxs ++ [{Id, V}]}.

%% --- Operation: validator ---

validator_pre(S) ->
    S#s.account_idxs /= [].

validator_args(S) ->
    [S#s.val_ctr, elements([Id || {Id, _} <- S#s.account_idxs])].

validator_pre(S, [_, Owner]) ->
    lists:keymember(Owner, 1, S#s.account_idxs).

validator(_, Owner) ->
    [{Addr, {_Pub, _Priv, SigFun}}] = test_utils:generate_keys(1),
    #validator{owner = Owner,
               addr = Addr,
               sig_fun = SigFun}.

validator_next(S, V, [Ctr, Owner]) ->
    S#s{validator_idxs = S#s.validator_idxs ++ [{Ctr, V, Owner}],
        val_ctr = Ctr + 1}.


%% --- Operation: coinbase ---
tx_coinbase_pre(S) ->
    S#s.height == 0 andalso unused_accounts(S) /= [].

%% only 1 coinbase Tx per account
tx_coinbase_args(S) ->
    [elements(unused_accounts(S)), ?initial_balance].

tx_coinbase_pre(S, [Id, _Balance]) ->
    lists:member(Id, unused_accounts(S)).  %% for shrinking

tx_coinbase(S, Id, Balance) ->
    blockchain_txn_coinbase_v1:new(account_address(S, Id), Balance).

tx_coinbase_next(S, SymbTx, [Id, Balance]) ->
    S#s{txs = S#s.txs ++ [#{kind => coinbase, account => Id, balance => Balance, sym => SymbTx}]}.

%% --- Operation: tx_consensus ---
tx_consensus_pre(S) ->
    S#s.height == 0 andalso
        unused_validators(S) /= [] andalso
        nr_txs(S, consensus) =< ?initial_validators.

tx_consensus_args(S) ->
    ?LET(Ctr, elements(unused_validators(S)),
         [Ctr, validator_owner(S, Ctr), ?min_stake]).

tx_consensus_pre(S, [Ctr, Owner, _]) ->
    %% only 1 consensus Tx per validator
    %% There must be a coinbase for the owner
    lists:member(Ctr, unused_validators(S)) andalso
        [ consensus || {C, _, O} <- S#s.validator_idxs,
                       C == Ctr andalso O == Owner,
                       lists:member(Owner, [Id || #{kind := coinbase, account := Id} <- S#s.txs]) ] /= [].  %% for shrinking

tx_consensus(S, Ctr, Owner, Stake) ->
    blockchain_txn_gen_validator_v1:new(validator_address(S, Ctr),
                                        account_address(S, Owner), Stake).

tx_consensus_next(S, SymbTx, [Ctr, Owner, Stake]) ->
    S#s{txs = S#s.txs ++ [#{kind => consensus, validator => Ctr, account => Owner, stake => Stake, sym => SymbTx}]}.

%% --- Operation: stake ---
tx_stake_pre(S) ->
    S#s.height > 0 andalso
        unused_validators(S) /= [].

tx_stake_args(S) ->
    ?LET({Ctr, _OldCtr}, {elements(unused_validators(S)), elements(S#s.staked)},
         [Ctr, validator_owner(S, Ctr), ?min_stake]).

tx_stake_pre(S, [Ctr, Owner, Stake]) ->
    tx_stake_valid(S, [Ctr, Owner, Stake]).

tx_stake_valid(S, [Ctr, Owner, Stake]) ->
    %% only 1 stake Tx per validator
    %% There must be an account for the owner (or a tx that creates an account but that's for later)
    lists:member(Ctr, unused_validators(S)) andalso
        [ account || {C, _, O} <- S#s.validator_idxs,
                     C == Ctr andalso O == Owner,
                     case lists:keyfind(Owner, 1, S#s.accounts) of
                         {_, _, HasStake} -> HasStake >= Stake;
                         _ -> false
                     end] /= [].  %% for shrinking

tx_stake(S, Ctr, Owner, Stake) ->
    Val = get_validator(S, Ctr),
    Account = get_account(S, Owner),
    Txn = blockchain_txn_stake_validator_v1:new(
            Val#validator.addr, Account#account.address,
            Stake,
            35000
           ),
    blockchain_txn_stake_validator_v1:sign(Txn, Account#account.sig_fun).

tx_stake_next(S, SymbTx, [Ctr, Owner, Stake]) ->
    S#s{txs = S#s.txs ++ [#{kind => stake, validator => Ctr, account => Owner, stake => Stake, sym => SymbTx}]}.




%% --- Operation: transfer stake ---
%% tx_transfer_pre(S) ->
%%      S#s.height > 0 andalso S#s.validator_idxs /= [].

%% tx_transfer_args(S) ->
%%     AccountIdxs = [ Id || {Id, _} <- S#s.account_idxs ],
%%     ?LET(OldCtr, elements(S#s.group),
%%     ?LET({From, Ctr}, elements([ {Owner, Ctr} || {Ctr, _, Owner} <- S#s.validator_idxs ]),
%%          [From, elements(AccountIdxs), choose(0, 40000), OldCtr]).

%% tx_transfer_pre(S, [From, To, _, Validator]) ->
%%     lists:keymember(From, 1, S#s.account_idxs) andalso
%%         lists:keymember(To, 1, S#s.account_idxs) andalso
%%         lists:keymember(Validator, 1, S#s.validator_idxs).

%% tx_transfer(S, From, To, Amount, Val) ->
%%     FromAccount = proplists:get_value(From, S#s.account_idxs),
%%     ToAccount = proplists:get_value(To, S#s.account_idxs),

%%     Txn = blockchain_txn_transfer_validator_stake_v1:new(
%%             account_address(FromAccount), address oldctr
%%             validator_address(S, Val),
%%             account_address(FromAccount),
%%             account_address(ToAccount),
%%             ?min_stake,
%%             Amount,
%%             35000
%%            ),
%%     STxn0 = blockchain_txn_transfer_validator_stake_v1:sign(Txn, FromAccount#account.sig_fun),
%%     blockchain_txn_transfer_validator_stake_v1:new_owner_sign(STxn0, ToAccount#account.sig_fun).

%% tx_transfer_next(S, SymbTx, [From, To, Amount, Validator]) ->
%%     S#s{txs =  S#s.txs ++ [{transfer, From, To, Amount, Validator, SymbTx}]}.


%% --- Operation: genesis_txs ---
genesis_txs_pre(S) ->
    S#s.chain /= undefined
        andalso nr_txs(S, coinbase) > 0
        andalso nr_txs(S, consensus) == ?initial_validators
        andalso S#s.height == 0.

genesis_txs_args(_S) ->
    [].

genesis_txs(S) ->
    Transactions = S#s.txs,
    {InitialVars, _MasterKeys} = blockchain_ct_utils:create_vars(val_vars()),

    GenPaymentTxs =
        [ Tx || #{kind := coinbase, sym := Tx} <- Transactions],

    InitialConsensusTxn =
        [Tx || #{kind := consensus, sym := Tx} <- Transactions ],

    GenConsensusGroupTx = blockchain_txn_consensus_group_v1:new(
                           [ validator_address(S, Ctr) || #{kind := consensus, validator := Ctr} <- Transactions],
                            <<"proof">>, 1, 0),

    Txs = InitialVars ++
        GenPaymentTxs ++
        InitialConsensusTxn ++
        [GenConsensusGroupTx],

    GenesisBlock = blockchain_block:new_genesis_block(Txs),
    ok = blockchain:integrate_genesis(GenesisBlock, S#s.chain),
    {ok, H} = blockchain:height(S#s.chain),
    H.

genesis_txs_next(S, _Value, []) ->
    S#s{height = 1,
        accounts = update_accounts(S, S#s.txs),
        used_validators = [ Ctr || #{kind := consensus, validator := Ctr} <- S#s.txs ],
        group = [ Ctr || #{kind := consensus, validator := Ctr} <- S#s.txs ],
        staked = [ Ctr || #{kind := consensus, validator := Ctr} <- S#s.txs ],
        txs = []}.   %% delete txs from pool

genesis_txs_post(_S, [], Res) ->
    eq(Res, 1).

%% --- Operation: genesis_txs ---
add_block_pre(S) ->
    S#s.height > 0 andalso S#s.group /= []. %% andalso S#s.txs /= [].

add_block_args(_S) ->
    [].

add_block(S) ->
    Chain = S#s.chain,
    Transactions =  [ Tx || #{sym := Tx} <- S#s.txs ],

    STxns = lists:sort(fun blockchain_txn:sort/2, Transactions),
    io:format("Transactions to validate to block: ~p\n", [STxns]),
    {Valid, _Invalid} = blockchain_txn:validate(STxns, Chain),

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
    io:format("Mblock ~p\n", [MBlock]),
    Block0 = blockchain_block_v1:new(MBlock),
    BinBlock = blockchain_block:serialize(Block0),
    Group = [ Val || {Id, Val, _} <- S#s.validator_idxs,
                     lists:member(Id, S#s.group)],
    Signatures = [ {Addr, Sign(BinBlock)} || #validator{addr = Addr, sig_fun = Sign} <- Group ],
    io:format("Signatures ~p\n", [Signatures]),
    Block1 = blockchain_block:set_signatures(Block0, Signatures),
    io:format("Block1 ~p\n", [Block1]),
    ok = blockchain:add_block(Block1, Chain),
    {ok, H} = blockchain:height(S#s.chain),
    {H, Valid}.


add_block_next(S, _Value, []) ->
    S#s{height = S#s.height + 1,
        accounts = update_accounts(S, S#s.txs),
        %% validators = update_validators(S#s.validators, Txs),
        txs = []}.   %% delete txs from pool

add_block_post(S, [], {Height, ValidTxs}) ->
    WronglyRejected = [ Tx || #{sym := Txn} = Tx <- S#s.txs,
                              not lists:member(Txn, ValidTxs),
                              is_valid(S, Tx)],
    ValidTxns =  [ Txn || #{sym := Txn} = Tx <- S#s.txs, is_valid(S, Tx)],
    eqc_statem:conj(
      [ eqc_statem:tag(height, eq(Height, S#s.height + 1)),
        eqc_statem:tag(invalid_accepted, eq(ValidTxs -- ValidTxns, [])),
        eqc_statem:tag(valid_reject,  eq(WronglyRejected, [])) ]).


is_valid(S, #{kind := transfer, account := From, account := To, amount := Amount, validator := Validator}) ->
    case lists:keyfind(From, 1, S#s.accounts) of
        {_, Balance, _Stake} ->
            Balance > Amount + 35000;
         false -> false
    end andalso lists:keymember(To, 1, S#s.account_idxs)
        andalso lists:member(Validator, unused_validators(S));
is_valid(_S, _) ->
    %% cannot use precondition (or valid) when creating stake, because now added to txs and hence no longer unused validator
    true.

%% Observational operations ---------------------------------------------------

%% --- Operation: balance ---
balances_pre(S) ->
    S#s.height > 0.

balances_args(S) ->
    [sublist([ Id || {Id, _, _} <- S#s.accounts ])].

balances(S, Ids) ->
    Ledger = blockchain:ledger(S#s.chain),
    [ case account_address(S, Id) of
          undefined -> {Id, undefined};
          Address ->
              {Id, case blockchain_ledger_v1:find_entry(Address, Ledger) of
                       {ok, Ent} -> blockchain_ledger_entry_v1:balance(Ent);
                       _ -> undefined
                   end}
      end || Id <- Ids ].

balances_post(S, [_Ids], Res) ->
    lists:all(fun({Id, RealBalance}) ->
                      case lists:keyfind(Id, 1, S#s.accounts) of
                          {_, Balance, _} ->
                              eq(RealBalance, Balance);
                          _ ->
                              eq(RealBalance, undefined)
                      end
              end, Res).

%% --- Operation: staked ---
staked_pre(S) ->
    S#s.height > 0.

staked_args(_S) ->
    [].

staked(S) ->
    Ledger = blockchain:ledger(S#s.chain),
    Circ = blockchain_ledger_v1:query_circulating_hnt(Ledger),
    Cool = blockchain_ledger_v1:query_cooldown_hnt(Ledger),
    Staked = blockchain_ledger_v1:query_staked_hnt(Ledger),
    {Staked, Circ, Cool}.

staked_post(S, [], {Staked, Circ, Cool}) ->
    eqc_statem:conj(
      [eqc_statem:tag(staked, eq(Staked, length(S#s.staked) * ?min_stake)),
       eqc_statem:tag(circ, eq(Circ, (length(S#s.accounts) * 2 * ?min_stake))),
       eqc_statem:tag(cool, eq(Cool, 0 * ?min_stake))   %% actually pending *
      ]).

staked_features(_S, [], {Staked, Circ, Cool}) ->
    [{cool, Cool}, {staked, Staked}, {circ, Circ}].



%%% ----------------------------------------

weight(S, validator) ->
    if length(S#s.validator_idxs) - length(S#s.used_validators) < ?initial_validators -> 20;
       true -> 1
    end;
weight(S, tx_coinbase) ->
    NrTxs = nr_txs(S, coinbase),
    if NrTxs =< 4 -> 10;
       true -> 1
    end;
weight(S, tx_consensus) ->
    NrTxs = nr_txs(S, consensus),
    if NrTxs < ?initial_validators -> 20;
       true -> 10
    end;
weight(S, tx_stake) ->
    NrTxs = nr_txs(S, stake),
    if S#s.height == 0 -> 0;
        NrTxs < ?initial_validators -> 20;
       NrTxs > 5 -> 1;
       true -> 2
    end;
weight(_, _) ->
    1.


%% -- Property ---------------------------------------------------------------
%% prop_stake() ->
%%     with_parameters(
%%       [{show_states, false},  % make true to print state at each transition
%%        {print_counterexample, true}],
prop_stake_txs() ->
    fault_rate(1, 20,
    ?FORALL(
       %% default to longer commands sequences for better coverage
       Cmds, more_commands(2, commands(?M)),
       %% Cmds, noshrink(more_commands(5, commands(?M))),
       begin
           %% these should be idempotent
           _ = application:ensure_all_started(lager),
           _ = blockchain_lock:start_link(),
           application:set_env(blockchain, test_mode, true),

           %% fresh dir for each chain
           BaseDir = make_base_dir(),
           {H, S, Res} = run_commands(Cmds, [{basedir, BaseDir}]),

           %% cleanup
           os:cmd("rm -r " ++ filename:join(".", BaseDir)),

           measure(height, S#s.height,
           aggregate(command_names(Cmds),
           aggregate(with_title("abstract transactions"), [ maps:without([sym], Tx) || Tx <- S#s.txs],
           aggregate(call_features(H),
           features(call_features(H),
           eqc_statem:pretty_commands(?M,
                                      Cmds,
                                      {H, S, Res},
                                      Res == ok))))))
       end)).

%%% helpers

validator_address(S, Ctr) ->
    case lists:keyfind(Ctr, 1, S#s.validator_idxs) of
        {_, #validator{addr = Addr}, _} ->
            Addr;
        _ ->
            undefined
    end.

validator_owner(S, Ctr) ->
    case lists:keyfind(Ctr, 1, S#s.validator_idxs) of
        {_, _, Owner} ->
            Owner;
        _ ->
            undefined
    end.

validator_address(#validator{addr = Addr}) ->
    Addr.

get_validator(S, Ctr) ->
    case lists:keyfind(Ctr, 1, S#s.validator_idxs) of
        {_, Val, _} ->
            Val;
        _ ->
            undefined
    end.

get_account(S, Id) ->
    proplists:get_value(Id, S#s.account_idxs).

account_address(#account{address = Addr}) ->
    Addr.

account_address(S, Id) ->
    case lists:keyfind(Id, 1, S#s.account_idxs) of
        {Id, #account{address = Addr}} ->
            Addr;
        _ ->
            undefined
    end.

update_accounts(S, []) ->
    S#s.accounts;
update_accounts(S, [#{kind := coinbase, account := Id, balance := Balance} | Txs]) ->
    case {lists:keyfind(Id, 1, S#s.account_idxs), lists:keyfind(Id, 1, S#s.accounts)} of
        {false, _} ->
            update_accounts(S, Txs);
        {_, {_, B, Stk}} ->
            NewAccounts = lists:keyreplace(Id, 1, S#s.accounts, {Id, B + Balance, Stk}),
            update_accounts(S#s{accounts = NewAccounts}, Txs);
        {_, false} ->
            update_accounts(S#s{accounts = S#s.accounts ++ [{Id, Balance, 0}]}, Txs)
    end;
update_accounts(S, [#{kind := consensus, account := Id, stake := Stake} | Txs]) ->
    case {lists:keyfind(Id, 1, S#s.account_idxs), lists:keyfind(Id, 1, S#s.accounts)} of
        {false, _} ->
            update_accounts(S, Txs);
        {_, {_, B, Stk}} ->
            NewAccounts = lists:keyreplace(Id, 1, S#s.accounts, {Id, B, Stake + Stk}),
            update_accounts(S#s{accounts = NewAccounts}, Txs);
        {_, false} ->
            update_accounts(S#s{accounts = S#s.accounts ++ [{Id, 0, Stake}]}, Txs)
    end;
update_accounts(S, [_ | Txs]) ->
    update_accounts(S, Txs).


nr_txs(S, Kind) ->
  length([K || #{kind := K} <- S#s.txs, K == Kind]).

unused_accounts(S) ->
    [ Id || {Id, _} <- S#s.account_idxs ] --
        [maps:get(account, Tx) || Tx <- S#s.txs, maps:get(kind, Tx) == coinbase].

unused_validators(S) ->
    [ Id || {Id, _, _} <- S#s.validator_idxs ] --
        ([Val || #{validator := Val} <- S#s.txs] ++ S#s.staked).
