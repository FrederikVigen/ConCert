(** * Oracle part of the Minter *)
(** This file contains the oracle part of the minter which is the part that can be called to distribute the fees to the correct parties from the Contract_Address
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/oracle_interface.mligo
*)

Require Import Blockchain.
Require Import Storage.
Require Import Oracle_Interface.
Require Import Types.
Require Import List.
Require Import ZArith.
Require Import Containers.
Require Import Fees_Lib.
Require Import Monads.
Require Import RecordUpdate.
Require Import Storage.
Require Import ContractCommon.
Import ListNotations.

Section Oracle.
Open Scope N.
Context {BaseTypes : ChainBase}.

(** * Division function with remainer and divided *)
(** Top-Level function for LIGOLang. Divides two numbers and returns the quotient and remainder.
    Returns None if [y] is 0.*)
Definition ediv (x : N) (y : N) : option (N * N) :=
    match y with
    | 0 => None
    | y =>
        let quotient := x / y in
        let remainder := x mod y in
        Some (quotient, remainder)
    end.

(** * Unused get balance functionality *)
Definition balance_sheet_or_default (k : Address) (token : TokenAddress) (ledger : TokenLedger) : N :=
    match FMap.find (k, token) ledger with
    | Some v => v
    | _ => 0
    end.

(** ** Calculates the share from a quantity *)
(** IMPORTANT: THIS FUNCTION IGNORES THE REMAINDER ON DIVISON *)
Definition tez_share (quantity : N) (share : N) : N :=
    let r := quantity * share in
    match ediv r 100 with
    | Some (q, r) => q
    | None => 0
    end.

(** ** Equivalent to tez_share functionality *)
Definition token_share (quantity : N) (share: N) : N :=
    let r := quantity * share in
    match ediv r 100 with
    | Some (q, r) => q
    | None => 0
    end.

(** ** Type definition for share percentage for specific addresses *)
Definition share_per_address : Type := Address * N.

(** ** Updates a ledger to the state after distribution of tokens *)
(** This includes subtraction of the distributed tokens from the total tokens *)
Definition token_for_share (ctx : ContractCallContext) (shares : list share_per_address) (token_address : TokenAddress) (ledger : TokenLedger) : option TokenLedger :=
    let total := token_balance ledger ctx.(ctx_contract_address) token_address in
    if total =? 0 then
        Some ledger
    else
        let apply :  (N * TokenLedger) -> share_per_address -> (N * TokenLedger) :=
            (fun (acc : (N * TokenLedger)) (share : share_per_address) =>
                let (distributed, distribution) := acc in
                let (receiver_address, percent) := share in
                let token_fees := token_share total percent in
                let updated_ledger := inc_token_balance distribution receiver_address token_address token_fees in
                (distributed +  token_fees, updated_ledger)
            ) in
        
        let (distributed, new_distribution) := fold_left apply shares (0, ledger) in
        do v <- sub total distributed ;
        Some (FMap.update (ctx.(ctx_contract_address), token_address) (Some v) new_distribution).

(** ** Runs token_for_share on a list of tokens *)
Definition tokens_for_share (ctx : ContractCallContext) (s : list share_per_address) (tokens : list TokenAddress) (ledger : TokenLedger) : option TokenLedger :=
    fold_left
        (fun (l_opt : option TokenLedger) (t : TokenAddress)  => 
            do l <- l_opt ;
            token_for_share ctx s t l)
        tokens
        (Some ledger).

(** ** Tries to find an address from a given key *)
(** IMPORTANT : Implicit address is not implemented in concert, this means that the implicit address here defaults to the contract_address which is indeed wrong *)
Definition key_or_registered_address (ctx : ContractCallContext) (k : N) (s : FMap N Address) : Address :=
    match FMap.find k s with
    | Some v => v
    | None => ctx.(ctx_contract_address)
    end.

(** ** Returns a list of shares based on the signers which includes de devpool_address and staking_address*)
Definition shares (ctx : ContractCallContext) (p : list N) (signers_in : FMap N Address) (governance : GovernanceStorage) : list share_per_address :=
    let signers_count := N.of_nat (length p) in
    let other_shares := [(governance.(dev_pool_address), governance.(fees_share_rec).(dev_pool)); (governance.(staking_address), governance.(fees_share_rec).(staking))] in
    fold_left 
        ( fun (acc : list share_per_address) (k : N) =>
            (key_or_registered_address ctx k signers_in, governance.(fees_share_rec).(signers) / signers_count) :: acc
        )
        p
        other_shares.

(** ** The actual distribute method combining all of the above functionality for tokens *)
Definition distribute_tokens (ctx : ContractCallContext) (p : DistributeParam ) (s : State) : option FeesStorage := 
    let fees_storage := s.(fees) in
    let governance := s.(governance) in
    let shares' := shares ctx p.(dp_signers) fees_storage.(fees_storage_signers) governance in 
    do new_ledger <- tokens_for_share ctx shares' p.(dp_tokens) fees_storage.(fees_storage_tokens) ;
    Some (fees_storage<| fees_storage_tokens := new_ledger |>).

(** ** Inner function of distribute functionality *)
Definition apply_distribute_xtz (total : N) (acc: N * XTZLedger) (share : share_per_address) : (N * XTZLedger) :=
    let (distributed, distribution) := acc in
    let (receiver_address, percent) := share in
    let tez_fees := tez_share total percent in
    let new_ledger := inc_xtz_balance distribution receiver_address tez_fees in
    (distributed + tez_fees, new_ledger).

(** ** The actual distribute method combining all of the above functionality for xtz *)
Definition distribute_xtz (ctx : ContractCallContext) (p : list N) (s : State) : FeesStorage :=
    let fees_storage := s.(fees) in
    let total := xtz_balance fees_storage.(fees_storage_xtz) ctx.(ctx_contract_address) in
    if total =? 0
    then fees_storage
    else
        let governance := s.(governance) in
        let shares := shares ctx p fees_storage.(fees_storage_signers) governance in
        let (distributed, new_distribution) := fold_left (apply_distribute_xtz total) shares (0, fees_storage.(fees_storage_xtz)) in
        let remaining := total - distributed in
        let new_distribution := FMap.update ctx.(ctx_contract_address) (Some remaining) new_distribution in
        fees_storage<| fees_storage_xtz := new_distribution |>.

(** ** The Main entrypoint of the Oracle part of the Minter contract*)
Definition oracle_main (ctx : ContractCallContext) (p : OracleEntrypoint) (s : State) : option ReturnType :=
    match p with
    | Distribute_xtz p => Some (s<| fees := distribute_xtz ctx p s|>, [])
    | Distribute_tokens p => 
        do fees_new <- distribute_tokens ctx p s ;
        Some (s<| fees := fees_new |>, [])
    end.

End Oracle.