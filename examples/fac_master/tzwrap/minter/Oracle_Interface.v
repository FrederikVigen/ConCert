Require Import Blockchain.
Require Import ZArith.
Require Import Serializable.

Section Oracle_Interface.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Record DistributeParam  := mkDistributeParam { 
    dp_signers : list N ;
    dp_tokens : list (Address * N)
}.
            
Inductive OracleEntrypoint :=
| Distribute_tokens (distribute_param : DistributeParam)
| Distribute_xtz (hash_list : list N).

Global Instance DistributeParam_serializable : Serializable DistributeParam :=
    Derive Serializable DistributeParam_rect<mkDistributeParam>.

Global Instance OracleEntrypoint_serializable : Serializable OracleEntrypoint :=
    Derive Serializable OracleEntrypoint_rect<Distribute_tokens, Distribute_xtz>.

End Oracle_Interface.