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

         validators = [],   %% [{nat(), #validator{}}] valid validators for account N
         used_validators = [],   %% cannot be used again?
         group,   %% validators for those that have stake?
         chain_accounts, %% the real accounts

         accounts, %% {nat(), Amount1, Amount2}
         patron, %% zero account
         height = 0,
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
      Cmd == genesis_txs; Cmd == unstake ->
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

%% --- Operation: patron ---
validator_pre(S) ->
    length(S#s.validators) < ?initial_validators.

validator_args(_S) ->
    [0, ?min_stake].

validator_pre(S, [Owner, _]) ->
    lists:keymember(Owner, 1, S#s.accounts).

validator(Owner, Stake) ->
    [{Addr, {_Pub, _Priv, SigFun}}] = test_utils:generate_keys(1),
    #validator{owner = Owner,
               addr = Addr,
               sig_fun = SigFun,
               stake = Stake}.

validator_next(S, V, [Owner, Stake]) ->
    S#s{validators = S#s.validators ++ [{Owner, V, 0}],
        txs = S#s.txs ++ [{validate_stake, Owner, Stake}]}.


%% --- Operation: init_accounts ---
init_accounts_pre(S) ->
    length(S#s.accounts) =< ?initial_validators.

init_accounts_args(S) ->
    [length(S#s.accounts), ?initial_balance].

init_accounts(Id, Balance) ->
    [{Addr, {Pub, Priv, SigFun}}] = test_utils:generate_keys(1),
    #account{id = Id,
             address = Addr,
             balance = Balance,
             sig_fun = SigFun,
             pub = Pub,
             priv = Priv}.

init_accounts_next(S, V, [Id, Balance]) ->
    S#s{accounts = S#s.accounts ++ [{Id, V, 0, 0}],
        txs = S#s.txs ++ [{coinbase, Id, Balance}]}.

%% --- Operation: genesis_txs ---
genesis_txs_pre(S) ->
    S#s.chain /= undefined andalso length(S#s.accounts) > ?initial_validators
        andalso length(S#s.validators) >= ?initial_validators
        andalso S#s.height == 0.

genesis_txs_args(S) ->
    [S#s.txs].

genesis_txs(S, Transactions) ->
    {InitialVars, _MasterKeys} = blockchain_ct_utils:create_vars(val_vars()),

    GenPaymentTxs = [blockchain_txn_coinbase_v1:new(Addr, Balance)
                     || {coinbase, Id, Balance} <- Transactions,
                        {Account, #account{address = Addr}, _, _} <- S#s.accounts,
                        Account == Id],

    InitialConsensusTxn =
        [blockchain_txn_gen_validator_v1:new(Addr, GenOwner#account.address, ?min_stake)
         || {validate_stake, Id, _Stake} <- Transactions,
            {Val, #account{address = Addr}, _} <- S#s.validators,
            {Account, GenOwner, _, _} <- S#s.accounts,
            Val == Id andalso Account == Id ],

    GenConsensusGroupTx = blockchain_txn_consensus_group_v1:new(
                           [Addr || {validate_stake, Id, _Stake} <- Transactions,
                                    {Val, #account{address = Addr}, _} <- S#s.validators],
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
        accounts = update_accounts(S#s.accounts, Txs),
        validators = update_validators(S#s.validators, Txs),
        group = [ V || {validator_stake, Id, _} <- Txs,
                       {Id, V, _} <- S#s.validators ],
        txs = []}.   %% delete txs from pool

genesis_txs_post(_S, [_], Res) ->
    eq(Res, 1).





update_accounts(Accounts, []) ->
    Accounts;
update_accounts(Accounts, [{coinbase, Id, Balance} | Txs]) ->
    NewAccounts = lists:map(fun({AId, RA, B, S}) when AId == Id ->
                                    {AId, RA, B + Balance, S};
                               (Account) ->
                                    Account
                            end, Accounts),
    update_accounts(NewAccounts, Txs);
update_accounts(Accounts, [_ | Txs]) ->
    update_accounts(Accounts, Txs).

update_validators(Vals, []) ->
    Vals;
update_validators(Vals, [{validator_stake, Id, Stake} | Txs]) ->
    NewVals = lists:map(fun({VId, RV, S}) when VId == Id ->
                                    {VId, RV, S + Stake};
                               (Val) ->
                                    Val
                            end, Vals),
    update_accounts(NewVals, Txs);
update_validators(Vals, [_ | Txs]) ->
    update_validators(Vals, Txs).



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
           eqc_statem:pretty_commands(?M,
                                      Cmds,
                                      {H, S, Res},
                                      Res == ok))))
       end)).

%%% helpers

abstract_tx_to_txn(Accounts, {payment, From, To, _Tokens}) ->
    FromAccount = maps:get(From, Accounts),
    ToAccount = maps:get(To, Accounts),
    {FromAccount, ToAccount}.


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
