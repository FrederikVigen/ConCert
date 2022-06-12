(** * Governance part of the Minter Contract *)
(** The content of this file is the governance part of the minters functionality 
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/governance.mligo
*)

Require Import Blockchain.
Require Import Storage.
Require Import Governance_Interface.
Require Import ZArith.
Require Import List.
Require Import Monads.
Require Import ContractCommon.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.

Open Scope N.
Section Governance.
Context {BaseTypes : ChainBase}.

(** ** Fail if the caller is not the governance contract*)
Definition fail_if_not_governance (ctx: ContractCallContext) (s : GovernanceStorage) : option unit :=
    if address_eqb ctx.(ctx_from) s.(contract) then
    Some tt
    else None.

(** ** Set the ERC 20 Wrapping fees *)
Definition set_erc_20_wrapping_fees (v : N) (s : GovernanceStorage) : GovernanceStorage :=
    s<|erc20_wrapping_fees := v|>.

(** ** Set the ERC 20 Unwrapping fees *)
Definition set_erc_20_unwrapping_fees (v : N) (s : GovernanceStorage) : GovernanceStorage :=
    s<|erc20_unwrapping_fees := v|>.

(** ** Set the 721 wrapping fees *)
Definition set_erc_721_wrapping_fees (v : N) (s : GovernanceStorage) : GovernanceStorage :=
    s<|erc721_wrapping_fees := v|>.
    
(** ** Set the ERC 721 unwrapping fees *)
Definition set_erc_721_unwrapping_fees (v : N) (s : GovernanceStorage) : GovernanceStorage :=
    s<|erc721_unwrapping_fees := v|>.

(** ** Set new governance contract *)
Definition set_governance (new_governance : Address) (s : GovernanceStorage) : GovernanceStorage :=
    s<|contract := new_governance|>.
    
(** ** The Main entrypoint for the governance part of the Minter*)
Definition governance_main (ctx : ContractCallContext) (p : GovernanceEntrypoints) (s : GovernanceStorage) : option (list ActionBody * GovernanceStorage) :=
    match p with
    | Set_erc20_wrapping_fees n => Some ([], set_erc_20_wrapping_fees n s)
    | Set_erc20_unwrapping_fees n => Some ([], set_erc_20_unwrapping_fees n s)
    | Set_erc721_wrapping_fees n => Some ([], set_erc_721_wrapping_fees n s)
    | Set_erc721_unwrapping_fees n => Some ([], set_erc_721_unwrapping_fees n s)
    | Set_governance a => Some ([], set_governance a s)
    | Set_dev_pool p => Some ([], s<|dev_pool_address := p|>)
    | Set_staking p => Some ([], s<|staking_address := p|>)
    | Set_fees_share param => 
        do _ <- throwIf (negb ((param.(dev_pool) + param.(staking) + param.(signers)) =? 100)) ;
        Some ([], s<|fees_share_rec := param|>)
    end.

End Governance.