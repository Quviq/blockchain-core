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
-include_lib("eqc/include/eqc_mocking.hrl").
%% We cannot use eqc_components, wrap_call due to wrap_call conflict

-include_lib("stdlib/include/assert.hrl").

-include_lib("blockchain/include/blockchain_vars.hrl").
-include_lib("blockchain/include/blockchain.hrl").

-compile([export_all, nowarn_export_all, nowarn_unused_record]).

-behaviour(eqc_statem).

%% -- State and state functions ----------------------------------------------

%-record

-record(s,
        {
         chain_group = [],   %% validators for those that have stake?
         chain_staked = [],
         chain_unstaked = [],
         chain_transferred = [],
         chain_accounts = [], %% Delayed version of accounts, updated when we create a block

         txs = [],   %% abstract transactions to be submitted for next block

         group = [],
         staked = [],
         unstaked = [],
         transferred = [],
         accounts = [],   %% {index, balance, stake}
         void = [],  %% void validators, cannot be used again

         height = 0,
         election_height = 0,
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
         address,
         sig_fun
        }).

-record(account,
        {
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
    Digits = integer_to_list(os:system_time(millisecond) rem 10000000),
    "stake-txns-dir-"++Digits.

val_vars() ->
    #{
      ?election_version => 5,    %% TODO also test for lower versions?
      ?validator_version => 2,
      ?validator_minimum_stake => ?min_stake,
      ?validator_liveness_grace_period => 100,
      ?validator_liveness_interval => 2000,
      ?stake_withdrawal_cooldown => 2,
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
                                   balances, stakes,
                                   tx_transfer, tx_coinbase, tx_consensus,
                                   tx_stake, tx_unstake, tx_transfer, tx_election,
                                   neg_tx_stake]),
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

create_account(_) ->
    [{Addr, {_, _, SigFun}}] = test_utils:generate_keys(1),
    #account{address = Addr,
             sig_fun = SigFun}.

create_account_next(S, V, [Id]) ->
    S#s{account_idxs = S#s.account_idxs ++ [{Id, V}]}.

%% --- Operation: validator ---

validator_args(S) ->
    [length(S#s.validator_idxs)].

validator(_) ->
    [{Addr, {_Pub, _Priv, SigFun}}] = test_utils:generate_keys(1),
    #validator{address = Addr,
               sig_fun = SigFun}.

validator_next(S, V, [Idx]) ->
    S#s{validator_idxs = S#s.validator_idxs ++ [{Idx, V}]}.


%% Transactions

%% We have a 2 step process. In order to generate a transaction, we look at the state on chain
%% as well as earlier created transactions. For example, there might be unused validators on
%% chain that are already used in a transaction.
%% Moreover, we may have enough balance on chain, but the balance has been reduced by transactions.
%% For generation, one would like to know a priori whether a transaction is valid, but that means
%% that we need to update the state with more than only the transaction. In other words, the
%% new state is the state of accepting valid and rejecting invalid transactions.
%% TODO: update 'kind' to invalid for those transactions that we know are not going to
%% make it on chain.

%% --- Operation: coinbase ---
tx_coinbase_pre(S) ->
    S#s.height == 0 andalso unused_accounts(S) /= [].

%% only 1 coinbase Tx per account
tx_coinbase_args(S) ->
    [elements(unused_accounts(S)), choose(?initial_balance, 2 * ?initial_balance)].

tx_coinbase_pre(S, [Id, _Balance]) ->
    lists:member(Id, unused_accounts(S)).  %% for shrinking

tx_coinbase(S, Id, Balance) ->
    blockchain_txn_coinbase_v1:new(account_address(S, Id), Balance).

tx_coinbase_next(S, SymbTx, [Id, Balance]) ->
    S#s{txs = S#s.txs ++ [#{kind => coinbase, account => Id, balance => Balance, sym => SymbTx}],
        accounts = S#s.accounts ++ [{Id, Balance, 0}]}.

%% --- Operation: tx_consensus ---
tx_consensus_pre(S) ->
    S#s.height == 0 andalso
        S#s.accounts /= [] andalso
        unused_validators(S) /= [] andalso
        length(S#s.group) =< ?initial_validators.

tx_consensus_args(S) ->
    ?LET({Ctr, {Id, _, _}}, {elements(unused_validators(S)), elements(S#s.accounts)},
         [Ctr, Id, ?min_stake + 3]).

%% for shrinking, make sure shrunk examples are still valid
tx_consensus_pre(S, [Ctr, Owner, _]) ->
    %% only 1 consensus Tx per validator
    %% There must be a coinbase for the owner
    lists:member(Ctr, unused_validators(S)) andalso
        lists:keymember(Owner, 1, S#s.accounts).

tx_consensus(S, Ctr, Owner, Stake) ->
    Val = get_validator(S, Ctr),
    Account = get_account(S, Owner),
    blockchain_txn_gen_validator_v1:new(Val#validator.address,
                                        Account#account.address, Stake).

tx_consensus_next(S, SymbTx, [Ctr, Owner, Stake]) ->
    {Owner, B, Stk} = lists:keyfind(Owner, 1, S#s.accounts),
    S#s{txs = S#s.txs ++ [#{kind => consensus, validator => Ctr, account => Owner, stake => Stake, sym => SymbTx}],
        accounts = lists:keyreplace(Owner, 1, S#s.accounts, {Owner, B, Stake + Stk}),
        group = S#s.group ++ [ Ctr ],
        staked = S#s.staked ++ [ #{idx => Ctr, stake => Stake, owner => Owner} ]}.

%% --- Operation: stake ---
%% Moving balance to stake

tx_stake_pre(S) ->
    S#s.height > 0 andalso
        unused_validators(S) /= [].

tx_stake_args(S) ->
    ?LET(Fault, fault(elements([used_validator, bad_sig, too_little_stake, too_much_stake]),
                      stake),
    ?LET({Ctr, {Id, _, _}}, {inject(S, used_validator, Fault, elements(unused_validators(S))),
                             elements(S#s.accounts)},
         [Fault, Ctr, Id, inject(S, too_much_stake, Fault, inject(S, too_little_stake, Fault, ?min_stake))])).

tx_stake_pre(S, [Fault, Ctr, Owner, Stake]) ->
    lists:keymember(Owner, 1, S#s.account_idxs) andalso
        lists:keymember(Ctr, 1, S#s.validator_idxs) andalso
        case Fault of
            stake ->
                valid_order(S, {stake, Owner}) andalso
                    tx_stake_valid(S, [Ctr, Owner, Stake]);
            _ ->
                not tx_stake_valid(S, [Ctr, Owner, Stake])
        end.

tx_stake_valid(S, [Ctr, Owner, Stake]) ->
    lists:member(Ctr, unused_validators(S)) andalso
        case lists:keyfind(Owner, 1, S#s.accounts) of
            {_, Balance, _} -> Balance >= Stake;
            _ -> false
        end.

tx_stake(S, Fault, Ctr, Owner, Stake) ->
    Val = get_validator(S, Ctr),
    Account = get_account(S, Owner),
    SigFun =
        case Fault of
            bad_sig -> Val#validator.sig_fun;
            _       -> Account#account.sig_fun
        end,
    Txn = blockchain_txn_stake_validator_v1:new(
            Val#validator.address, Account#account.address,
            Stake,
            35000
           ),
    blockchain_txn_stake_validator_v1:sign(Txn, SigFun).

tx_stake_next(S, SymbTx, [stake, Ctr, Owner, Stake]) ->
    {Owner, B, Stk} = lists:keyfind(Owner, 1, S#s.accounts),
    S#s{txs = S#s.txs ++ [#{kind => stake, validator => Ctr, account => Owner, stake => Stake, sym => SymbTx}],
        accounts = lists:keyreplace(Owner, 1, S#s.accounts, {Owner, B - Stake, Stk + Stake}),
        staked = S#s.staked ++ [#{idx => Ctr, stake => Stake, owner => Owner}]};
tx_stake_next(S, SymbTx, [Fault, Ctr, Owner, Stake]) ->
    S#s{txs = S#s.txs ++ [#{kind => Fault, validator => Ctr, account => Owner, stake => Stake, sym => SymbTx}]}.

%% One can either use same operation to produce both valid and invalid transactions,
%% or use one operation for guaranteed positive and one for guaranteed negative transactions.


%% --- Operation: unstake ---
%% Moving balance from stake at future height

tx_unstake_pre(S) ->
    S#s.height > 0 andalso
       S#s.staked /= [].

tx_unstake_args(S) ->
    CoolDown = maps:get(?stake_withdrawal_cooldown, val_vars()),
    ?LET(Kind, fault(elements([unstake_from_group, unstake_wrong_stake, short_cooldown, bad_sig, wrong_owner]),
                     unstake),
    ?LET({Ctr, Stake, Owner}, elements([{Ctr, Stake, Owner} || #{idx := Ctr, stake := Stake, owner := Owner} <- S#s.staked,
                                                               Kind /= unstake_from_group orelse lists:member(Ctr, S#s.group)]),
         [Kind, Ctr, inject(S, wrong_owner, Kind, Owner),
          inject(S, unstake_wrong_stake, Kind, Stake),
          inject(S, short_cooldown, Kind, choose(CoolDown, CoolDown + 3))])).

tx_unstake_pre(S, [Kind, Ctr, Owner, Stake, DeltaHeight]) ->
    lists:keymember(Owner, 1, S#s.account_idxs) andalso
    lists:keymember(Ctr, 1, S#s.validator_idxs) andalso
    (Kind /= unstake orelse
                       (valid_order(S, {unstake, Owner}) andalso
                        tx_unstake_valid(S, [Ctr, Owner, Stake, DeltaHeight]))).

tx_unstake_valid(S, [Ctr, Owner, Stake, _DeltaHeight]) ->
    lists:member(Ctr, [Id || #{idx := Id, stake:= Stk, owner := A} <- S#s.staked,
                             not lists:member(Id, S#s.group),
                             Stk == Stake,
                             Owner == A]) andalso
        not lists:keymember(Ctr, 1, S#s.unstaked).

tx_unstake(S, Fault, Ctr, Owner, Stake, DeltaHeight) ->
    Val = get_validator(S, Ctr),
    Account = get_account(S, Owner),
    SigFun =
        case Fault of
            bad_sig -> Val#validator.sig_fun;
            _       -> Account#account.sig_fun
        end,
    Txn = blockchain_txn_unstake_validator_v1:new(
            Val#validator.address, Account#account.address,
            Stake,
            S#s.height + DeltaHeight,
            35000
           ),
    blockchain_txn_unstake_validator_v1:sign(Txn, SigFun).

tx_unstake_next(S, SymbTx, [Kind, Ctr, Owner, Stake, DeltaHeight]) ->
    Tx = #{kind => Kind, validator => Ctr, account => Owner, height => S#s.height + DeltaHeight, sym => SymbTx},
    case Kind of
        unstake ->
            S#s{txs = S#s.txs ++ [Tx],
                unstaked = S#s.unstaked ++ [{Ctr, Stake, S#s.height + DeltaHeight}],
                void = S#s.void ++ [Ctr || not lists:member(Ctr, S#s.void)]};
        _ ->
            S#s{txs = S#s.txs ++ [Tx]}
    end.   %% the next block handles this Tx

%% Oh dear,
%% if I unstake in block 2, (then my height+DeltaHeight is actually 6), so I ask to unstake at height 6.
%%     So I see effect already in block 6!! That's one too early if indeed the grace period should be 5

%% --- Operation: transfer ---

tx_transfer_pre(S) ->
    S#s.height > 0 andalso
        unused_validators(S) /= [] andalso
        [Ctr || #{idx := Ctr} <- S#s.staked,
                not lists:member(Ctr, S#s.group)] /= [].

tx_transfer_args(S) ->
    ?LET({NewCtr, {NewId, Balance, _}}, {elements(unused_validators(S)), elements(S#s.accounts)},
    ?LET({Ctr, Stake, Owner}, elements([{Ctr, Stake, Owner}
                                        || #{idx := Ctr, stake := Stake, owner := Owner} <- S#s.staked,
                                           not lists:member(Ctr, S#s.group)]),
         [Ctr, Owner, NewCtr, NewId, Stake, oneof([0, Balance div 2, ?bones(9000)])])).

tx_transfer_pre(S, [Ctr, Owner, NewCtr, NewOwner, Stake, Amount]) ->
    valid_order(S, {transfer, Owner, NewOwner}) andalso
        tx_transfer_valid(S, [Ctr, Owner,  NewCtr, NewOwner, Stake, Amount]).

tx_transfer_valid(S, [Ctr, Owner, NewCtr, NewOwner, Stake, Amount]) ->
    tx_unstake_valid(S, [Ctr, Owner, Stake, S#s.height]) andalso
        lists:member(NewCtr, unused_validators(S)) andalso
        case lists:keyfind(Owner, 1, S#s.accounts) of
            {_, _, Stk} -> Stk >= Stake;
            _ -> false
        end andalso
        case lists:keyfind(NewOwner, 1, S#s.accounts) of
            {_, Balance, _} -> Balance >= Amount;
            _ -> Amount == 0 andalso
                     lists:keyfind(NewOwner, 1, S#s.account_idxs) %% trying to create account?
        end.

tx_transfer(S, Ctr, Owner, NewCtr, NewOwner, Stake, Amount) ->
    Val = get_validator(S, Ctr),
    Account = get_account(S, Owner),
    NewVal = get_validator(S, NewCtr),
    NewAccount = get_account(S, NewOwner),
    Txn = blockchain_txn_transfer_validator_stake_v1:new(
            Val#validator.address,
            NewVal#validator.address,
            Account#account.address,
            NewAccount#account.address,
            Stake,
            Amount,
            35000
           ),
    STxn = blockchain_txn_transfer_validator_stake_v1:sign(Txn, Account#account.sig_fun),
    blockchain_txn_transfer_validator_stake_v1:new_owner_sign(STxn, NewAccount#account.sig_fun).

tx_transfer_next(S, SymbTx, [Ctr, Owner, NewCtr, NewOwner, Stake, Amount]) ->
    {Owner, B, Stk} = lists:keyfind(Owner, 1, S#s.accounts),
    S#s{txs = S#s.txs ++ [#{kind => transfer, validator => Ctr, account => Owner, stake => Stake,
                            new_account => NewOwner, new_validator => NewCtr, sym => SymbTx}],
        accounts =
            begin
                Accounts1 = lists:keyreplace(Owner, 1, S#s.accounts, {Owner, B + Amount, Stk - Stake}),
                case lists:keyfind(NewOwner, 1, Accounts1) of
                    false -> Accounts1 ++ [{NewOwner, -Amount, Stake}];   %% kind of weird
                    {NewOwner, NB, NStk} -> lists:keyreplace(NewOwner, 1, Accounts1, {NewOwner, NB - Amount, NStk + Stake})
                end
            end,
        staked = [ Staked || #{idx := Idx} = Staked <- S#s.staked, Idx /= Ctr] ++
            [#{idx => NewCtr, stake => Stake, owner => NewOwner}],
        transferred = S#s.transferred ++ [#{idx => NewCtr, stake => Stake, owner => NewOwner}],
        void = S#s.void ++ [Ctr || not lists:member(Ctr, S#s.void)]}.

%% --- Operation: election ---

tx_election_pre(S) ->
    S#s.height > 0 andalso
         nr_txs(S, election) == 0 andalso  %% I can handle only 1 election in one block in mock
       %% S#s.height - S#s.election_height > maps:get(?election_interval, val_vars()) andalso
       length([ Idx || #{idx := Idx} <-S#s.staked ]) > maps:get(?num_consensus_members, val_vars()).


%% possible error: duplicate_group,{1,1}  when reusing [0] as validators (group [0,1,2,3])
%%  no members when using unused validators or when list in new group is empty
%% wrong_members_size,{4,1} if there are less than 4 members

%% This cannot shrink nicely.. since hashes change when shrinking and selection depends on hash
tx_election_args(S) ->
    ConsensusMbrs = maps:get(?num_consensus_members, val_vars()),
    ?LET(Fault, case S#s.height - S#s.election_height < maps:get(?election_interval, val_vars()) of
                   true -> wrong_election_height;
                   false -> fault(elements([election_no_member || unused_validators(S) /= []] ++
                                               [election_nr_members]),
                                  election)
               end,
    ?LET(Staked, oneof([S#s.group, noshrink(shuffle([ Idx || #{idx := Idx} <- S#s.staked]))]),
    ?LET(NewCandidates, inject(S, election_no_member, Fault, Staked),
    ?LET(FirstN, inject(S, election_nr_members, Fault, min(ConsensusMbrs, length(NewCandidates))),
         [Fault, lists:sublist(NewCandidates, FirstN)])))).

tx_election_pre(S, [Kind, NewGroup]) ->
    lists:all(fun(Ctr) -> lists:keymember(Ctr, 1, S#s.validator_idxs) end,
              NewGroup) andalso
        case Kind of
            election -> tx_election_valid(S, [NewGroup]);
            _ -> not tx_election_valid(S, [NewGroup])
        end.

tx_election_valid(S, [NewGroup]) ->
    length(NewGroup) == maps:get(?num_consensus_members, val_vars()) andalso
        S#s.height - S#s.election_height >= maps:get(?election_interval, val_vars()) andalso
        NewGroup /= S#s.group andalso %%% needed ??
        NewGroup -- [Idx || #{idx := Idx} <- S#s.staked] == [].

tx_election(S, _, SymNewGroup) ->
    NewGroup = [ Val || {Id, Val} <- S#s.validator_idxs,
                        lists:member(Id, SymNewGroup)],
    NewGroupAddresses = [ Addr || #validator{address = Addr} <- NewGroup],
    eqc_mocking:init_lang(?REPLICATE(?EVENT(blockchain_election, new_group, ['_', '_', '_', '_'],
                                                  NewGroupAddresses))),
    Artifact = term_to_binary(NewGroupAddresses),
               %% Note that this choice binds the implementation strongly to Erlang (version)
    Signatures = [ {Addr, Sign(Artifact)} || #validator{address = Addr, sig_fun = Sign} <- NewGroup ],
    Proof = term_to_binary(Signatures, [compressed]),
    blockchain_txn_consensus_group_v1:new(NewGroupAddresses, Proof, S#s.height, 0).

tx_election_next(S, SymbTx, [Kind, NewGroup]) when Kind /= election ->
    S#s{txs = S#s.txs ++ [#{kind => Kind, group => NewGroup, sym => SymbTx}]};
tx_election_next(S, SymbTx, [election, NewGroup]) ->
    %% Election is first, forget all other transactions and revert state
    S#s{txs = [#{kind => election, group => NewGroup, sym => SymbTx}],
        accounts = S#s.chain_accounts,
        staked = S#s.chain_staked,
        unstaked = S#s.chain_unstaked,
        group = NewGroup,
        void = S#s.void ++ [ Ctr || Ctr <- NewGroup, not lists:member(Ctr, S#s.void)]}.


%% --- Operation: genesis_txs ---
genesis_txs_pre(S) ->
    S#s.chain /= undefined
        andalso length(S#s.accounts) > 0
        andalso length(S#s.group) == ?initial_validators
        andalso S#s.height == 0.

genesis_txs_args(_S) ->
    [].

genesis_txs(S) ->
    Transactions = S#s.txs,
    {InitialVars, _MasterKeys} = blockchain_ct_utils:create_vars(val_vars()),

    GenPaymentTxs =
        [ Tx || #{kind := coinbase, sym := Tx} <- Transactions],

    InitialConsensusTxn =
        [ Tx || #{kind := consensus, sym := Tx} <- Transactions ],

    GenConsensusGroupTx = blockchain_txn_consensus_group_v1:new(
                           [ validator_address(S, Ctr) || Ctr <- S#s.group],
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
        chain_accounts = S#s.accounts,
        chain_group = S#s.group,
        chain_staked = S#s.staked,
        void = S#s.group,
        txs = []}.   %% delete txs from pool

genesis_txs_post(_S, [], Res) ->
    eq(Res, 1).

genesis_txs_features(S, [], _Res) ->
    [{tx, Kind} || #{kind := Kind} <- S#s.txs ].

%% --- Operation: genesis_txs ---
add_block_pre(S) ->
    S#s.height > 0.

%% here we can take a subset of group to sign (>= 4 members).
add_block_args(S) ->
    [S#s.chain_group].

add_block_pre(S, [Group]) ->
    Group == S#s.chain_group.  %% TODO take valid subset

add_block(S, Signers) ->
    Chain = S#s.chain,
    Transactions =  [ Tx || #{sym := Tx} <- S#s.txs ],

    STxns = lists:sort(fun blockchain_txn:sort/2, Transactions),
    %% io:format("Transactions to validate to block: ~p\n", [STxns]),
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
    Block0 = blockchain_block_v1:new(MBlock),
    BinBlock = blockchain_block:serialize(Block0),
    Group = [ Val || {Id, Val} <- S#s.validator_idxs,
                     lists:member(Id, Signers)],
    Signatures = [ {Addr, Sign(BinBlock)} || #validator{address = Addr, sig_fun = Sign} <- Group ],
    Block1 = blockchain_block:set_signatures(Block0, Signatures),
    ok = blockchain:add_block(Block1, Chain),
    {ok, H} = blockchain:height(S#s.chain),
    {H, Valid}.


add_block_next(S0, _Value, [_]) ->
    S = adapt_height(S0, S0#s.height + 1),
    HasValidElection = nr_txs(S, election) > 0,
    S#s{chain_accounts = S#s.accounts,
        chain_staked = S#s.staked,
        chain_unstaked = S#s.unstaked,
        chain_group = S#s.group,
        election_height = if HasValidElection -> S#s.height;  %% +1 ??
                             true -> S#s.election_height
                          end,
        txs = []}.

add_block_post(S, [_], {Height, AcceptedTxs}) ->
    ModelValidTxs = valid_txs(S),
    WronglyRejected = [ Tx || #{sym := Txn} = Tx <- ModelValidTxs,
                              not lists:member(Txn, AcceptedTxs)],
    ValidTxns =  [ Txn || #{sym := Txn} <- ModelValidTxs],
    eqc_statem:conj(
      [ eqc_statem:tag(height, eq(Height, S#s.height + 1)),
        eqc_statem:tag(invalid_accepted, eq(AcceptedTxs -- ValidTxns, [])),
        eqc_statem:tag(valid_reject, eq(WronglyRejected, [])) ]).


add_block_features(S, [_], {_, Valid}) ->
    [ {tx, Kind} || #{kind := Kind} <- S#s.txs ] ++
        [ {txs_per_block, length(Valid)} ].

valid_txs(S) ->
    [ Tx || #{kind := Kind} = Tx <- S#s.txs,
            lists:member(Kind, [stake, unstake, transfer, election])].


%% Observational operations ---------------------------------------------------

%% --- Operation: balance ---
balances_pre(S) ->
    S#s.height > 0.

balances_args(S) ->
    [sublist([ Id || {Id, _, _} <- S#s.chain_accounts ])].

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
    eqc_statem:conj(
      [ case lists:keyfind(Id, 1, S#s.chain_accounts) of
            {_, Balance, _} ->
                eq(RealBalance, Balance);
            _ ->
                eq(RealBalance, undefined)
        end || {Id, RealBalance} <- Res ]).


%% --- Operation: staked ---
stakes_pre(S) ->
    S#s.height > 0.

stakes_args(_S) ->
    [].

stakes(S) ->
    Ledger = blockchain:ledger(S#s.chain),
    Circ = blockchain_ledger_v1:query_circulating_hnt(Ledger),
    Cool = blockchain_ledger_v1:query_cooldown_hnt(Ledger),
    Staked = blockchain_ledger_v1:query_staked_hnt(Ledger),
    {Staked, Circ, Cool}.

stakes_post(S, [], {Staked, Circ, Cool}) ->
    ModelUnstaked = lists:sum([Stk || {_, Stk, _H} <- S#s.chain_unstaked ]),
    ModelStaked = lists:sum([Stk || #{stake := Stk} <- S#s.chain_staked]) - ModelUnstaked,
    ModelTotalBalance = lists:sum([B || {_, B, _Stk} <- S#s.chain_accounts]),
    eqc_statem:conj(
      [eqc_statem:tag(staked, eq(Staked, ModelStaked)),  %% Staked in group ??
       eqc_statem:tag(circ, eq(Circ, ModelTotalBalance)),
       eqc_statem:tag(cool, eq(Cool, lists:sum([Stk || {_, Stk, _} <- S#s.chain_unstaked])))
      ]).



%%% ----------------------------------------

weight(_S, init_chain) ->
    50;
weight(S, validator) ->
    Unused = length(unused_validators(S)),
    if Unused == 0 -> 20;
       Unused > 2 -> 0;
       true -> 1
    end;
weight(S, create_account) ->
    Unused = length(unused_accounts(S)),
    if Unused == 0 -> 20;
       Unused > 3 -> 1;
       true -> 1
    end;
weight(S, tx_coinbase) ->
    NrTxs = nr_txs(S, coinbase),
    if NrTxs =< 8 -> 20;
       true -> 0
    end;
weight(S, tx_consensus) ->
    NrTxs = nr_txs(S, consensus),
    if NrTxs < ?initial_validators -> 20;
       true -> 10
    end;
weight(S, tx_stake) ->
    NrTxs = nr_txs(S, stake),
    NrOther = nr_txs(S, unstake),
    Election = (nr_txs(S, election) /= 0),
    if Election -> 0;
       S#s.height == 0; NrOther > 0 -> 0;
       NrTxs < 5 -> 3 * 20;
       true -> 2
    end;
weight(S, tx_unstake) ->
    NrTxs = nr_txs(S, unstake),
    NrOther = nr_txs(S, transfer),
    Election = (nr_txs(S, election) /= 0),
    if Election -> 0;
       S#s.height == 0; NrOther > 0 -> 0;
       NrTxs < 5 -> 2 * 20;
       true -> 2
    end;
weight(S, tx_transfer) ->
    NrTxs = nr_txs(S, transfer),
    Election = (nr_txs(S, election) /= 0),
    if Election -> 0;
        NrTxs < ?initial_validators -> 20;
       NrTxs > 5 -> 1;
       true -> 2
    end;
weight(S, tx_election) ->
    ElectionInterval = maps:get(?election_interval, val_vars()),
    if S#s.height rem ElectionInterval /= 0 -> 1;
       true -> 20
    end;
weight(_, _) ->
    10.


%% -- Property ---------------------------------------------------------------
%% prop_stake() ->
%%     with_parameters(
%%       [{show_states, false},  % make true to print state at each transition
%%        {print_counterexample, true}],
prop_stake_txs() ->
    prop_stake_txs(#{loglevel => error}).

prop_stake_txs(Opts) ->
    fault_rate(maps:get(fault_percent, Opts, 5), 100,
    ?SETUP(fun() ->
                   _ = application:ensure_all_started(lager),
                   lager:set_loglevel(lager_console_backend, maps:get(loglevel, Opts, info)),
                   %% Warning this is a bit ugly, but we need to mock rand
                   %% ok = code:unstick_dir(filename:dirname(code:which(rand))),
                   eqc_mocking:start_mocking(api_spec()),
                   fun() ->
                           %% Put original rand module back
                           eqc_mocking:stop_mocking()
                   end
           end,
    ?FORALL(Cmds, more_commands(5, commands(?M)),
       begin
           {ok, Pid} = blockchain_lock:start_link(),
           application:set_env(blockchain, test_mode, true),

           %% fresh dir for each chain
           BaseDir = make_base_dir(),
           {H, S, Res} = run_commands(Cmds, [{basedir, BaseDir}]),

           %% cleanup
           unlink(Pid),
           exit(Pid, kill),
           os:cmd("rm -r " ++ filename:join(".", BaseDir)),

           {TxsPerBlock, Features} =
               lists:foldl(fun({txs_per_block, A}, {PBs, Fs}) ->
                                   {[A|PBs], Fs};
                              (F, {PBs, Fs}) ->
                                   {PBs, [F|Fs]}
                           end, {[], []}, call_features(H)),
           measure(height, S#s.height,
           measure(accounts, length(S#s.accounts),
           aggregate(with_title(txs_per_block), TxsPerBlock,
           aggregate(command_names(Cmds),
           aggregate(Features,
           features(call_features(H),
           eqc_statem:pretty_commands(?M,
                                      Cmds,
                                      {H, S, Res},
                                      Res == ok)))))))
       end))).

api_spec() ->
    #api_spec{
       modules =
           [ %% #api_module{
             %%   name = rand, fallback = ?MODULE,
             %%   functions = [ #api_fun{ name = uniform, arity = 0 },
             %%                 #api_fun{ name = seed, arity = 2 }]}
             #api_module{
                name = blockchain_election,
                fallback = blockchain_election,
                functions = [ #api_fun{ name = new_group, arity = 4, fallback = false }
              %%            ]},
              %% #api_module{
              %%    name = blockchain_txn_consensus_group_v1,
              %%    fallback = blockchain_txn_consensus_group_v1,
              %%    functions = [ #api_fun{ name = is_valid, arity = 2 }
                             ]}
           ]}.



%% #api_fun{ name = seed, arity = 2, fallback = true }

%%% helpers

validator_address(S, Ctr) ->
    Val = get_validator(S, Ctr),
    Val#validator.address.

validator_idx(S, Address) ->
    case [ Idx || {Idx, #validator{address = A}} <- S#s.validator_idxs, A == Address ] of
        [Idx] ->
            Idx;
        _ ->
            error
    end.

get_validator(S, Ctr) ->
    case lists:keyfind(Ctr, 1, S#s.validator_idxs) of
        {_, Val} ->
            Val;
        _ ->
            undefined
    end.

get_account(S, Id) ->
    proplists:get_value(Id, S#s.account_idxs).

account_address(S, Id) ->
    case lists:keyfind(Id, 1, S#s.account_idxs) of
        {Id, #account{address = Addr}} ->
            Addr;
        _ ->
            undefined
    end.


nr_txs(S, Kind) ->
  length([K || #{kind := K} <- S#s.txs, K == Kind]).

unused_accounts(S) ->
    [ Id || {Id, _} <- S#s.account_idxs ] -- [ Id || {Id, _, _} <- S#s.accounts ].

unused_validators(S) ->
    [ Id || {Id, _} <- S#s.validator_idxs ] --
        (S#s.void ++ [ Ctr || #{idx := Ctr} <- S#s.staked ++ S#s.transferred ]).

adapt_height(S, Height) ->
    ReleaseStake = [ {Ctr, Stk, Owner}
                     || {Ctr, Stk, H} <- S#s.unstaked,
                        #{owner := Owner} <- [ Staked || #{idx := Idx} = Staked <- S#s.staked,
                                                         Ctr == Idx],
                        H =< Height ],
    S#s{height = Height,
        staked = [ Staked || #{idx := Ctr} = Staked <- S#s.staked,
                             not lists:keymember(Ctr, 1, ReleaseStake)],
        unstaked = [ {Ctr, Stk, H} || {Ctr, Stk, H} <- S#s.unstaked,
                                      not lists:keymember(Ctr, 1, ReleaseStake) ],
        accounts = lists:foldl(fun({_, Stk, Owner}, Accounts) ->
                                       {Id, B, Stake} = lists:keyfind(Owner, 1, Accounts),
                                       lists:keyreplace(Owner, 1, Accounts, {Id, B + Stk, Stake - Stk})
                               end, S#s.accounts, ReleaseStake)}.

inject(S, Kind, Kind, Gen) ->
    inject(S, Kind, Gen);
inject(_, _, _, Gen) ->
    Gen.

inject(_, unstake_wrong_stake, StakeGen) ->
    ?LET(Stake, StakeGen,
    ?LET({Pos, F}, {choose(1, 10), elements([fun(X) -> Stake + X end, fun(X) -> Stake - X end])},
         F(Pos)));
inject(_, short_cooldown, _) ->
    choose(0, maps:get(?stake_withdrawal_cooldown, val_vars()) - 1);
inject(_, too_little_stake, _) ->
    choose(-1, ?min_stake-1);
inject(_, too_much_stake, _) ->
    choose(?min_stake, 2 * ?min_stake - 1);
inject(S, wrong_owner, Owner) ->
    elements([Id || {Id, _, _} <- S#s.accounts, length(S#s.accounts) < 2 orelse Id /= Owner]);
inject(S, used_validator, _) ->
    elements(S#s.void);
inject(S, election_no_member, Staked) ->
    [ elements(unused_validators(S)) | Staked ];
inject(_S, election_nr_members, Nr) ->
    ?SUCHTHAT(N, choose(1, Nr), N /= maps:get(?num_consensus_members, val_vars()));
inject(_, Kind, Gen) ->
    eqc_messenger:message("undefined fault injection ~p", [Kind]),
    io:format("undefined fault injection ~p", [Kind]),
    Gen.

%% Ensure that transactions only are generated when they are in valid order
valid_order(S, {stake, _Owner}) ->
    [ x || #{kind := Kind} <- S#s.txs,
           Kind == unstake orelse Kind == transfer ] == [];
valid_order(S, {unstake, _Owner}) ->
    [ x || #{kind := Kind} <- S#s.txs,
           Kind == transfer ] == [];
    %% %% There is no unstake after a transfer for the same owner
    %% [ x || #{kind := transfer, account := A1, new_account := A2} <- S#s.txs] == [];
valid_order(_S, {transfer, _, _}) ->
    true.