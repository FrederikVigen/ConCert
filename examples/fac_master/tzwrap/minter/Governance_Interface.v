Require Import Storage.
Require Import ZArith.
Require Import Blockchain.
Require Import Types.


Section Governance_Interface.
Context {BaseTypes : ChainBase}.

Inductive GovernanceEntrypoints :=
| Set_erc20_wrapping_fees (p : bps)
| Set_erc20_unwrapping_fees (p : bps)
| Set_erc721_wrapping_fees (p : N)
| Set_erc721_unwrapping_fees (p : N)
| Set_fees_share (p : FeesShare)
| Set_governance  (p : Address)
| Set_dev_pool (p : Address)
| Set_staking (p : Address).

End Governance_Interface.