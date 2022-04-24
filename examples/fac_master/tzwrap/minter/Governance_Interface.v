Require Import Storage.
Require Import ZArith.
Require Import Blockchain.
Require Import Types.
Require Import Serializable.


Section Governance_Interface.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

Inductive GovernanceEntrypoints :=
| Set_erc20_wrapping_fees (p : bps)
| Set_erc20_unwrapping_fees (p : bps)
| Set_erc721_wrapping_fees (p : N)
| Set_erc721_unwrapping_fees (p : N)
| Set_fees_share (p : FeesShare)
| Set_governance  (p : Address)
| Set_dev_pool (p : Address)
| Set_staking (p : Address).

Global Instance GovernanceEntrypoints_serializable : Serializable GovernanceEntrypoints :=
    Derive Serializable GovernanceEntrypoints_rect<Set_erc20_wrapping_fees, Set_erc20_unwrapping_fees, Set_erc721_wrapping_fees, Set_erc721_unwrapping_fees, Set_fees_share, Set_governance, Set_dev_pool, Set_staking>.

End Governance_Interface.