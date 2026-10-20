(** End-to-end theorem for the exact dense 221-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K221F Require Import Dense221 Correct221.

Theorem tm221_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm221_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm221_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm221_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm221_halts_iff_ZFC_inconsistent.
Print Assumptions tm221_nonhalting_iff_ZFC_consistent.
