(** End-to-end theorem for the exact dense 227-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K227F Require Import Dense227 Correct227.

Theorem tm227_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm227_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm227_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm227_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm227_halts_iff_ZFC_inconsistent.
Print Assumptions tm227_nonhalting_iff_ZFC_consistent.
