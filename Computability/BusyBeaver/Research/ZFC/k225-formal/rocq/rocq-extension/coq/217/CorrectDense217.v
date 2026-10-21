(** End-to-end theorem for the exact dense 217-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K217F Require Import Dense217 Correct217.

Theorem tm217_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm217_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm217_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm217_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm217_halts_iff_ZFC_inconsistent.
Print Assumptions tm217_nonhalting_iff_ZFC_consistent.
