(** End-to-end theorem for the exact dense 229-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K230F Require Import Dense229 Correct229.

Theorem tm229_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm229_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm229_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm229_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm229_halts_iff_ZFC_inconsistent.
Print Assumptions tm229_nonhalting_iff_ZFC_consistent.
