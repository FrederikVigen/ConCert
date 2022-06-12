(** * Etherum library interface *)
(** This file contains a small interface for EthAddresses
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/ethereum_lib.mligo
*)

From Coq Require Import Cyclic31.

Section Etherum_Lib.

(** ** Event id consiting of block hash and log_index *)
Definition EthEventId : Type := N * N.

(** ** EthAddress which in LIGO is byes but in coq is N *)
Definition EthAddress : Type := N.


End Etherum_Lib.