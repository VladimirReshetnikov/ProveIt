(** End-to-end theorem for the exact dense 215-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K215F Require Import Dense215 Correct215.

Theorem tm215_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm215_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm215_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm215_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm215_halts_iff_ZFC_inconsistent.
Print Assumptions tm215_nonhalting_iff_ZFC_consistent.
