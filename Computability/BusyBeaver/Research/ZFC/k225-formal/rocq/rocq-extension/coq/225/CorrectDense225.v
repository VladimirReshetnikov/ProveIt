(** End-to-end theorem for the exact dense 225-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K225F Require Import Dense225 Correct225.

Theorem tm225_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm225_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm225_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm225_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm225_halts_iff_ZFC_inconsistent.
Print Assumptions tm225_nonhalting_iff_ZFC_consistent.
