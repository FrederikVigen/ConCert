(** * Cryptology functionality **)
(**
    This file is used to mock the Crypto API of LIGO.
    See https://ligolang.org/docs/reference/crypto-reference/
*)

Require Import ZArith.

Section Crypto.

(** ** Check signature functionality  *)
(**
    Mocks the check of a [signature] using public [key] and the [message]
    Normally in LIGO the message is packed using Bytes.pack (See https://ligolang.org/docs/reference/bytes-reference/)
    Which converts it into a binary format used for serilization.
    Since this methods mocks the check of a signature we simply pass the message as the type it is.
*)
Definition check_signature {A} (key : N) (signature : N) (message : A) :=
    true.

(** ** Mocked hashkey functionality *)
(**
    Mocks the [hash_key] function of the LIGO Crypto API.
*)
Definition hash_key (k : N) :=
    k.

End Crypto.