(** Integration-only client of the accepted K215 endpoint.
    CM215Stream.v was freshly compiled and recursively kernel-checked.
    This file requires the full accepted K215 closure and was not rebuilt here. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC.
From K215F Require Import Dense215 CorrectDense215.
Require Import CM215Stream.

Theorem cm215_halts_iff_ZFC_inconsistent :
  Dense.halts cm_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  transitivity (Dense.halts dense_tm Dense.c0).
  - symmetry. exact blank_halts_iff.
  - exact tm215_halts_iff_ZFC_inconsistent.
Qed.
Corollary cm215_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts cm_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite cm215_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions cm215_halts_iff_ZFC_inconsistent.
