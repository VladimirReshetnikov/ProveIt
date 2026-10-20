(** End-to-end theorem for the exact dense 226-state literal artifact. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K226F Require Import Dense226 Correct226.

Theorem tm226_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite dense_sparse_halts_iff.
  exact tm226_sparse_halts_iff_ZFC_inconsistent.
Qed.

Corollary tm226_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm226_halts_iff_ZFC_inconsistent. reflexivity. Qed.

Print Assumptions tm226_halts_iff_ZFC_inconsistent.
Print Assumptions tm226_nonhalting_iff_ZFC_consistent.
