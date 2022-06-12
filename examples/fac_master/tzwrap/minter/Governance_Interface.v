(** * Interface for the governance part of the Minter *)
(** The content o this file is the interface for the governance part of the Minter
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/governance_interface.mligo
*)

Require Import Storage.
Require Import ZArith.
Require Import Blockchain.
Require Import Types.
Require Import Serializable.


Section Governance_Interface.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

(** ** All of the governance entrypoints *)
Inductive GovernanceEntrypoints :=
| Set_erc20_wrapping_fees (p : bps)
| Set_erc20_unwrapping_fees (p : bps)
| Set_erc721_wrapping_fees (p : N)
| Set_erc721_unwrapping_fees (p : N)
| Set_fees_share (p : FeesShare)
| Set_governance  (p : Address)
| Set_dev_pool (p : Address)
| Set_staking (p : Address).

(* begin hide *)
Global Instance GovernanceEntrypoints_serializable : Serializable GovernanceEntrypoints :=
    Derive Serializable GovernanceEntrypoints_rect<Set_erc20_wrapping_fees, Set_erc20_unwrapping_fees, Set_erc721_wrapping_fees, Set_erc721_unwrapping_fees, Set_fees_share, Set_governance, Set_dev_pool, Set_staking>.
(* end hide*)

End Governance_Interface.