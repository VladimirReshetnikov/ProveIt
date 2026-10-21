(** Closed endpoint for the sparse-label 217-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K217F Require TM230 Sim230Main.
From K217F Require Import Source217 MainDom.
From K230S Require Import KQuotZFC.

Theorem tm217_sparse_halts_iff_ZFC_inconsistent :
  K217F.TM230.TM230.halts K217F.TM230.tm K217F.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite K217F.Sim230Main.tm230_rm, p217_dagDom.
  exact dagDom_iff_standardZFC.
Qed.
Corollary tm217_sparse_nonhalting_iff_ZFC_consistent :
  (~ K217F.TM230.TM230.halts K217F.TM230.tm K217F.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm217_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm217_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm217_sparse_nonhalting_iff_ZFC_consistent.
