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

(*  
    Top-Level function for LIGOLang. Divides two numbers and returns the quotient and remainder.
    Returns None if [y] is 0.
*)
Definition ediv (x : N) (y : N) : option (N * N) :=
    match y with
    | 0 => None
    | y =>
        let quotient := x / y in
        let remainder := x mod y in
        Some (quotient, remainder)
    end.

Definition balance_sheet_or_default (k : Address) (token : TokenAddress) (ledger : TokenLedger) : N :=
    match FMap.find (k, token) ledger with
    | Some v => v
    | _ => 0
    end.

Definition tez_share (quantity : N) (share : N) : N :=
    let r := quantity * share in
    match ediv r 100 with
    | Some (q, r) => q
    | None => 0
    end.

Definition token_share (quantity : N) (share: N) : N :=
    let r := quantity * share in
    match ediv r 100 with
    | Some (q, r) => q
    | None => 0
    end.

Definition share_per_address : Type := Address * N.

Definition token_for_share (ctx : ContractCallContext) (shares : list share_per_address) (token_address : TokenAddress) (ledger : TokenLedger) : option TokenLedger :=
    let total := token_balance ledger ctx.(ctx_contract_address) token_address in
    if total =? 0 then
        Some ledger
    else
        let apply : share_per_address -> (N * TokenLedger) -> (N * TokenLedger) :=
            (fun (share : share_per_address) (acc : (N * TokenLedger)) =>
                let (distributed, distribution) := acc in
                let (receiver_address, percent) := share in
                let token_fees := token_share total percent in
                let updated_ledger := inc_token_balance distribution receiver_address token_address token_fees in
                (distributed +  token_fees, updated_ledger)
            ) in
        
        let (distributed, new_distribution) := fold_right apply (0, ledger) shares in
        match maybe (total - distributed) with
        | None => None (* DISTRIBUTION_FAILED *)
        | Some v => Some (FMap.update (ctx.(ctx_contract_address), token_address) (Some v) new_distribution)
        end.
        
Definition tokens_for_share (ctx : ContractCallContext) (s : list share_per_address) (tokens : list TokenAddress) (ledger : TokenLedger) : option TokenLedger :=
    fold_right
        (fun (t : TokenAddress) (l_opt : option TokenLedger)  => 
            do l <- l_opt ;
            token_for_share ctx s t l)
        (Some ledger)
        tokens.

Definition key_or_registered_address (ctx : ContractCallContext) (k : N) (s : FMap N Address) : Address :=
    match FMap.find k s with
    | Some v => v
    | None => ctx.(ctx_contract_address) (* TODO: How do we handle implicit accounts *)
    end.

Definition shares (ctx : ContractCallContext) (p : list N) (signers_in : FMap N Address) (governance : GovernanceStorage) : list share_per_address :=
    let signers_count := N.of_nat (length p) in
    let other_shares := [(governance.(dev_pool_address), governance.(fees_share_rec).(dev_pool)); (governance.(staking_address), governance.(fees_share_rec).(staking))] in
    fold_right 
        ( fun (k : N) (acc : list share_per_address) =>
            (key_or_registered_address ctx k signers_in, governance.(fees_share_rec).(signers) / signers_count) :: acc
        )
        other_shares
        p.

Definition distribute_tokens (ctx : ContractCallContext) (p : DistributeParam ) (s : State) : option FeesStorage := 
    let fees_storage := s.(fees) in
    let governance := s.(governance) in
    let shares' := shares ctx p.(dp_signers) fees_storage.(fees_storage_signers) governance in 
    do new_ledger <- tokens_for_share ctx shares' p.(dp_tokens) fees_storage.(fees_storage_tokens) ;
    Some (fees_storage<| fees_storage_tokens := new_ledger |>).

Definition distribute_xtz (ctx : ContractCallContext) (p : list N) (s : State) : FeesStorage :=
    let fees_storage := s.(fees) in
    let total := xtz_balance fees_storage.(fees_storage_xtz) ctx.(ctx_contract_address) in
    if total =? 0
    then fees_storage
    else
        let governance := s.(governance) in
        let shares := shares ctx p fees_storage.(fees_storage_signers) governance in

        let apply : share_per_address -> (N * XTZLedger) -> (N * XTZLedger) :=
            (
                fun (share : share_per_address) (acc : (N * XTZLedger))  =>
                    let (distributed, distribution) := acc in
                    let (receiver_address, percent) := share in
                    let tez_fees := tez_share total percent in
                    let new_ledger := inc_xtz_balance distribution receiver_address tez_fees in
                    (distributed + tez_fees, new_ledger)
            ) in
        let (distributed, new_distribution) := fold_right apply (0, fees_storage.(fees_storage_xtz)) shares in
        let remaining := total - distributed in
        let new_distribution := FMap.update ctx.(ctx_contract_address) (Some remaining) new_distribution in
        fees_storage<| fees_storage_xtz := new_distribution |>.


Definition oracle_main (ctx : ContractCallContext) (p : OracleEntrypoint) (s : State) : option ReturnType :=
    match p with
    | Distribute_xtz p => Some (s<| fees := distribute_xtz ctx p s|>, [])
    | Distribute_tokens p => 
        do fees_new <- distribute_tokens ctx p s ;
        Some (s<| fees := fees_new |>, [])
    end.

End Oracle.