(** * The interface for the Oracle part of the Minter Contract *)
(** This file contains some type definitions for the Oracle.v file which is the Oracle part of the Minter Contract
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/oracle_interface.mligo
*)

Require Import Blockchain.
Require Import ZArith.
Require Import Serializable.

Section Oracle_Interface.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

(** ** Input parameters to distribution of tokens *)
Record DistributeParam  := mkDistributeParam { 
    dp_signers : list N ;
    dp_tokens : list (Address * N)
}.
            
(** ** The Oracle parts entrypoints*)
Inductive OracleEntrypoint :=
| Distribute_tokens (distribute_param : DistributeParam)
| Distribute_xtz (hash_list : list N).

(* begin hide *)
Global Instance DistributeParam_serializable : Serializable DistributeParam :=
    Derive Serializable DistributeParam_rect<mkDistributeParam>.

Global Instance OracleEntrypoint_serializable : Serializable OracleEntrypoint :=
    Derive Serializable OracleEntrypoint_rect<Distribute_tokens, Distribute_xtz>.
(* end hide *)

End Oracle_Interface.