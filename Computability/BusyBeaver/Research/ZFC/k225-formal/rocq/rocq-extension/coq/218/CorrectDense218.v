(** End-to-end theorem for the exact dense 218-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K218F Require Import Dense218 Correct218.

Theorem tm218_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm218_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm218_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm218_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm218_halts_iff_ZFC_inconsistent.
Print Assumptions tm218_nonhalting_iff_ZFC_consistent.
