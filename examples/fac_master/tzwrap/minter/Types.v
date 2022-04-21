From Coq Require Import Cyclic31.
From Coq Require Import String.

Require Import Blockchain.

Section Types.
Context {BaseTypes : ChainBase}.

Definition bps := N.

Definition MetaData := string -> positive.

Definition TokenAddress : Type := (Address * N).

End Types.