(** Exact literal context215 table attached to ProveIt's existing sparse endpoint. *)
Require Import NativeContext LiteralBindings NativeSparseAdapter.
Theorem context_literal_blank_halts_iff_sparse :
  NativeContext.halts LiteralBindings.literal_new NativeContext.blank <->
  K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0.
Proof.
  rewrite <- LiteralBindings.context_literal_blank_halts_iff.
  exact NativeSparseAdapter.native_blank_halts_iff_sparse.
Qed.
Theorem context_literal_blank_nonhalts_iff_sparse :
  (~ NativeContext.halts LiteralBindings.literal_new NativeContext.blank) <->
  (~ K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0).
Proof. rewrite context_literal_blank_halts_iff_sparse. reflexivity. Qed.
Print Assumptions context_literal_blank_halts_iff_sparse.
Print Assumptions context_literal_blank_nonhalts_iff_sparse.
