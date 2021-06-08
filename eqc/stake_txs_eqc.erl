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
         chain,

         used_validators = [],   %% cannot be used again?
         group,   %% validators for those that have stake?
         validator_idxs = [],
         account_idxs = [],
           %% mapping from account to runtime account address and details
           %% Purposely using a list instead of a map

         accounts = [],   %% {index, balance, stake}
         validators = [], %% {index, owner, stake}  probably not needed
         height = 0,
         val_ctr = 0,
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

wrap_call(S, {call, Mod, Cmd, Args}) when
      Cmd == genesis_txs; Cmd == balances; Cmd == staked ->
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

%% --- Operation: validator ---
validator_pre(S) ->
    length(S#s.validator_idxs) < ?initial_validators.

validator_args(S) ->
    [S#s.val_ctr, 0, ?min_stake].

validator_pre(S, [_, Owner, _]) ->
    lists:keymember(Owner, 1, S#s.account_idxs).

validator(_, Owner, Stake) ->
    [{Addr, {_Pub, _Priv, SigFun}}] = test_utils:generate_keys(1),
    #validator{owner = Owner,
               addr = Addr,
               sig_fun = SigFun,
               stake = Stake}.

validator_next(S, V, [Ctr, Owner, Stake]) ->
    S#s{validator_idxs = S#s.validator_idxs ++ [{Ctr, V}],
        txs = S#s.txs ++ [{validate_stake, Ctr, Owner, Stake}],
        val_ctr = Ctr + 1}.


%% --- Operation: init_accounts ---
init_accounts_pre(S) ->
    length(S#s.account_idxs) =< ?num_accounts.

init_accounts_args(S) ->
    [length(S#s.account_idxs), ?initial_balance].

init_accounts(Id, _) ->
    [{Addr, {Pub, Priv, SigFun}}] = test_utils:generate_keys(1),
    #account{id = Id,
             address = Addr,
             sig_fun = SigFun,
             pub = Pub,
             priv = Priv}.

init_accounts_next(S, V, [Id, Balance]) ->
    S#s{account_idxs = S#s.account_idxs ++ [{Id, V}],
        txs = S#s.txs ++ [{coinbase, Id, Balance}]}.

%% --- Operation: genesis_txs ---
genesis_txs_pre(S) ->
    S#s.chain /= undefined andalso length(S#s.account_idxs) > ?initial_validators
        andalso length(S#s.validator_idxs) >= ?initial_validators
        andalso S#s.height == 0.

genesis_txs_args(S) ->
    [S#s.txs].

genesis_txs(S, Transactions) ->
    {InitialVars, _MasterKeys} = blockchain_ct_utils:create_vars(val_vars()),

    GenPaymentTxs =
        [ blockchain_txn_coinbase_v1:new(account_address(S, Id), Balance)
          || {coinbase, Id, Balance} <- Transactions,
             account_address(S, Id) /= undefined],

    InitialConsensusTxn =
        [blockchain_txn_gen_validator_v1:new(validator_address(S, Ctr), account_address(S, Owner), Stake)
         || {validate_stake, Ctr, Owner, Stake} <- Transactions ],

    GenConsensusGroupTx = blockchain_txn_consensus_group_v1:new(
                           [ validator_address(S, Ctr) || {validate_stake, Ctr, _, _} <- Transactions],
                            <<"proof">>, 1, 0),

    Txs = InitialVars ++
        GenPaymentTxs ++
        InitialConsensusTxn ++
        [GenConsensusGroupTx],

    GenesisBlock = blockchain_block:new_genesis_block(Txs),
    ok = blockchain:integrate_genesis(GenesisBlock, S#s.chain),
    {ok, H} = blockchain:height(S#s.chain),
    H.

genesis_txs_next(S, _Value, [Txs]) ->
    S#s{height = 1,
        accounts = update_accounts(S, Txs),
        %% validators = update_validators(S#s.validators, Txs),
        group = [ Ctr || {validate_stake, Ctr, _, _} <- Txs ],
        txs = []}.   %% delete txs from pool

genesis_txs_post(_S, [_], Res) ->
    eq(Res, 1).


%% --- Operation: balance ---
balances_pre(S) ->
    S#s.height > 0.

balances_args(S) ->
    [[ Id || {Id, _, _} <- S#s.accounts ]].

balances(S, Ids) ->
    Ledger = blockchain:ledger(S#s.chain),
    [ case account_address(S, Id) of
          undefined -> {Id, undefined};
          Address ->
              {ok, Ent} = blockchain_ledger_v1:find_entry(Address, Ledger),
              {Id, blockchain_ledger_entry_v1:balance(Ent)}
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

staked_post(S, [], {Staked, _Circ, Cool}) ->
    eqc_statem:conj(
      [eqc_statem:tag(staked, eq(Staked, length(S#s.group) * ?min_stake)),
       %% eqc_statem:tag(circ, eq(Circ, (?num_accounts * 2 - (length(S#s.group) - ?initial_validators) - NumPends) * ?min_stake,
       eqc_statem:tag(cool, eq(Cool, 0 * ?min_stake))   %% actually pending *
      ]).




%%% ----------------------------------------



%% -- Property ---------------------------------------------------------------
%% prop_stake() ->
%%     with_parameters(
%%       [{show_states, false},  % make true to print state at each transition
%%        {print_counterexample, true}],
prop_stake_txs() ->
    fault_rate(1, 20,
    ?FORALL(
       %% default to longer commands sequences for better coverage
       Cmds, more_commands(1, commands(?M)),
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
           aggregate(with_title("abstract transactions"), S#s.txs,
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
        {_, #validator{addr = Addr}} ->
            Addr;
        _ ->
            undefined
    end.

validator_address(#validator{addr = Addr}) ->
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
update_accounts(S, [{coinbase, Id, Balance} | Txs]) ->
    case {lists:keyfind(Id, 1, S#s.account_idxs), lists:keyfind(Id, 1, S#s.accounts)} of
        {false, _} ->
            update_accounts(S, Txs);
        {_, {_, B, Stk}} ->
            NewAccounts = lists:keyreplace(Id, 1, S#s.accounts, {Id, B + Balance, Stk}),
            update_accounts(S#s{accounts = NewAccounts}, Txs);
        {_, false} ->
            update_accounts(S#s{accounts = S#s.accounts ++ [{Id, Balance, 0}]}, Txs)
    end;
update_accounts(S, [{validator_stake, _Ctr, Id, Stake} | Txs]) ->
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
