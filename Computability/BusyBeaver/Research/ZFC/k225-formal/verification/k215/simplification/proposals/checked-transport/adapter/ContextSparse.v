(** Closed bridge from the new context-return machine to ProveIt's exact
    existing K215 sparse-machine halting predicate. *)
Require Import NativeContext NativeSparseAdapter.
Theorem context_blank_halts_iff_sparse :
  NativeContext.halts NativeContext.new NativeContext.blank <->
  K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0.
Proof.
  rewrite <- NativeContext.context_blank_halts_iff.
  exact NativeSparseAdapter.native_blank_halts_iff_sparse.
Qed.
Theorem context_blank_nonhalts_iff_sparse :
  (~ NativeContext.halts NativeContext.new NativeContext.blank) <->
  (~ K215F.TM230.TM230.halts K215F.TM230.tm K215F.TM230.TM230.c0).
Proof. rewrite context_blank_halts_iff_sparse. reflexivity. Qed.
Print Assumptions context_blank_halts_iff_sparse.
Print Assumptions context_blank_nonhalts_iff_sparse.
