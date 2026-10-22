(** Optional compatibility client; excluded from the K215 endpoint spine.
    The old compiler statement is available as CompilerDomCompat.compile.
    The old fully qualified L1_CompPerm.compile name is intentionally retired. *)
From K215F Require Import Thm222 ThmDom L1_CompPerm.

Lemma compile X : thmDom X -> exists L, blk X L.
Proof. intro H. apply compile_direct. now apply thm222_of_thmDom. Qed.
Print Assumptions compile.
