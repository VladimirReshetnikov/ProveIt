(* ===================================================================== *)
(*  Complete generic Mu-recursive decision for sextic radical formulas.  *)
(*                                                                       *)
(*  This file composes the proved reducible dispatcher with the generic  *)
(*  irreducible pair/triple assembly.  The four expensive arity-eight    *)
(*  cores remain ordinary arguments until their concrete evaluators and  *)
(*  semantic bridges are available.                                     *)
(* ===================================================================== *)

From Stdlib Require Import Bool Vector.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From PolynomialFormulas Require Import
  AbelRuffini SexticRecursiveCore SexticReducibleDecision
  SexticMuRecComputability
  SexticMuRecFactorDecision SexticMuRecFinalAssembly
  SexticMuRecIrreducibleAssembly SexticMuRecSemanticDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecCompleteDecision.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module FA := PolynomialFormulasSexticMuRecFinalAssembly.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module SD := PolynomialFormulasSexticMuRecSemanticDecision.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section CoreAssembly.

Variable pair_collision_core pair_root_core : Vector.t nat 8 -> bool.
Variable pair_collision_program pair_root_program : recalg 8.
Variable Hpair_collision_program :
  IA.core_boolean_spec pair_collision_core pair_collision_program.
Variable Hpair_root_program :
  IA.core_boolean_spec pair_root_core pair_root_program.
Variable pair_eventually :
  IA.guarded_projected_eventually pair_collision_core.

Variable triple_collision_core triple_root_core : Vector.t nat 8 -> bool.
Variable triple_collision_program triple_root_program : recalg 8.
Variable Htriple_collision_program :
  IA.core_boolean_spec triple_collision_core triple_collision_program.
Variable Htriple_root_program :
  IA.core_boolean_spec triple_root_core triple_root_program.
Variable triple_eventually :
  IA.guarded_projected_eventually triple_collision_core.

Variable Hpair_collision_exact :
  IA.pair_collision_core_exact pair_collision_core.
Variable Hpair_root_exact :
  IA.pair_root_core_exact pair_root_core.
Variable Htriple_collision_exact :
  IA.triple_collision_core_exact triple_collision_core.
Variable Htriple_root_exact :
  IA.triple_root_core_exact triple_root_core.

(* ------------------------------------------------------------------- *)
(* Complete decision on six encoded lower coefficients of a monic sextic. *)

Definition encoded_monic_sextic_radicalb
    (values : Vector.t nat 6) : bool :=
  if IA.encoded_factor_guard values
  then FA.encoded_monic_reducible_radicalb values
  else IA.encoded_irreducible_resolventb
    pair_collision_core pair_eventually pair_root_core
    triple_collision_core triple_eventually triple_root_core values.

Definition ra_encoded_monic_sextic_radical : recalg 6 :=
  FA.ra_boolean_if
    ra_encoded_monic_has_proper_factor
    FA.ra_encoded_monic_reducible_radical
    (IA.ra_encoded_irreducible_resolvent
      pair_collision_program pair_root_program
      triple_collision_program triple_root_program).

Lemma ra_encoded_monic_sextic_radical_correct values :
  ⟦ra_encoded_monic_sextic_radical⟧ values
    (bool_to_nat (encoded_monic_sextic_radicalb values)).
Proof.
unfold ra_encoded_monic_sextic_radical,
  encoded_monic_sextic_radicalb.
apply (FA.ra_boolean_if_correct
  IA.ra_encoded_factor_guard_correct
  FA.ra_encoded_monic_reducible_radical_correct
  (IA.ra_encoded_irreducible_resolvent_correct
    Hpair_collision_program Hpair_root_program pair_eventually
    Htriple_collision_program Htriple_root_program triple_eventually)).
Qed.

Definition encoded_monic_sextic_radical_relation
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_sextic_radicalb values).

Theorem encoded_monic_sextic_radical_relation_murec :
  MuRec_computable encoded_monic_sextic_radical_relation.
Proof.
unfold encoded_monic_sextic_radical_relation.
refine (@recalg_graph_murec 6
  (fun values => bool_to_nat (encoded_monic_sextic_radicalb values))
  ra_encoded_monic_sextic_radical _).
exact: ra_encoded_monic_sextic_radical_correct.
Qed.

Definition ra_encoded_monic_sextic_radical_code : recalg 1 :=
  ra_comp ra_encoded_monic_sextic_radical (ra_vec_project 6).

Lemma ra_encoded_monic_sextic_radical_code_correct code :
  ⟦ra_encoded_monic_sextic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_monic_sextic_radicalb (project 6 code))).
Proof.
unfold ra_encoded_monic_sextic_radical_code.
exists (project 6 code); split.
- exact: ra_encoded_monic_sextic_radical_correct.
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_sextic_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_sextic_radicalb (project 6 (vec_head code))).

Theorem encoded_monic_sextic_radical_code_relation_murec :
  MuRec_computable encoded_monic_sextic_radical_code_relation.
Proof.
unfold encoded_monic_sextic_radical_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_monic_sextic_radicalb (project 6 (vec_head code))))
  ra_encoded_monic_sextic_radical_code _).
intro values; vec split values with code; vec nil values.
exact: ra_encoded_monic_sextic_radical_code_correct.
Qed.

(* ------------------------------------------------------------------- *)
(* Exact agreement with the existing semantic monic dispatcher.        *)

Theorem encoded_monic_sextic_radicalb_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_sextic_radicalb
      (FD.encode_monic_sextic_coefficients f) =
  SD.projected_monic_sextic_radicalb f.
Proof.
rewrite /encoded_monic_sextic_radicalb
  /IA.encoded_factor_guard
  /SD.projected_monic_sextic_radicalb
  FD.encoded_monic_has_proper_factorb_mathcomp.
case hfactor: (SRC.has_bounded_proper_factor f).
- exact: FA.encoded_monic_reducible_radicalb_selected.
- exact: (IA.encoded_irreducible_resolventb_mathcomp
    pair_eventually Hpair_collision_exact Hpair_root_exact
    triple_eventually Htriple_collision_exact Htriple_root_exact
    hfactor).
Qed.

Theorem encoded_monic_sextic_radicalP (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves
      (SRD.rational_monic_sextic f))
    (encoded_monic_sextic_radicalb
      (FD.encode_monic_sextic_coefficients f)).
Proof.
rewrite encoded_monic_sextic_radicalb_mathcomp.
exact: SD.projected_monic_sextic_radicalP.
Qed.

Lemma encoded_monic_sextic_radical_relation_mathcomp
    (f : SRC.monic_sextic) out :
  encoded_monic_sextic_radical_relation
      (FD.encode_monic_sextic_coefficients f) out <->
  out = bool_to_nat (SD.projected_monic_sextic_radicalb f).
Proof.
rewrite /encoded_monic_sextic_radical_relation
  encoded_monic_sextic_radicalb_mathcomp.
reflexivity.
Qed.

Lemma encoded_monic_sextic_radical_code_relation_mathcomp
    (f : SRC.monic_sextic) out :
  encoded_monic_sextic_radical_code_relation
      (inject (FD.encode_monic_sextic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat (SD.projected_monic_sextic_radicalb f).
Proof.
rewrite /encoded_monic_sextic_radical_code_relation.
cbn [vec_head].
rewrite project_inject encoded_monic_sextic_radicalb_mathcomp.
reflexivity.
Qed.

Lemma encoded_monic_sextic_radical_exact :
  FA.encoded_monic_sextic_radical_exact
    encoded_monic_sextic_radicalb.
Proof. exact: encoded_monic_sextic_radicalb_mathcomp. Qed.

(* ------------------------------------------------------------------- *)
(* Specialization of the raw seven-vector and one-natural wrappers.     *)

Definition encoded_raw_sextic_radicalb
    (values : Vector.t nat 7) : bool :=
  FA.encoded_raw_sextic_radicalb
    encoded_monic_sextic_radicalb values.

Definition ra_encoded_raw_sextic_radical : recalg 7 :=
  FA.ra_encoded_raw_sextic_radical
    ra_encoded_monic_sextic_radical.

Lemma ra_encoded_raw_sextic_radical_correct values :
  ⟦ra_encoded_raw_sextic_radical⟧ values
    (bool_to_nat (encoded_raw_sextic_radicalb values)).
Proof.
exact: (FA.ra_encoded_raw_sextic_radical_correct
  ra_encoded_monic_sextic_radical_correct).
Qed.

Definition encoded_raw_sextic_radical_relation
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (encoded_raw_sextic_radicalb values).

Theorem encoded_raw_sextic_radical_relation_murec :
  MuRec_computable encoded_raw_sextic_radical_relation.
Proof.
change (MuRec_computable
  (FA.encoded_raw_sextic_radical_relation
    encoded_monic_sextic_radicalb)).
exact: (FA.encoded_raw_sextic_radical_relation_murec
  ra_encoded_monic_sextic_radical_correct).
Qed.

Definition encoded_raw_sextic_radical_codeb (code : nat) : bool :=
  encoded_raw_sextic_radicalb (project 7 code).

Definition ra_encoded_raw_sextic_radical_code : recalg 1 :=
  FA.ra_encoded_raw_sextic_radical_code
    ra_encoded_monic_sextic_radical.

Lemma ra_encoded_raw_sextic_radical_code_correct code :
  ⟦ra_encoded_raw_sextic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat (encoded_raw_sextic_radical_codeb code)).
Proof.
exact: (FA.ra_encoded_raw_sextic_radical_code_correct
  ra_encoded_monic_sextic_radical_correct).
Qed.

Definition encoded_raw_sextic_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_sextic_radical_codeb (vec_head code)).

Theorem encoded_raw_sextic_radical_code_relation_murec :
  MuRec_computable encoded_raw_sextic_radical_code_relation.
Proof.
change (MuRec_computable
  (FA.encoded_raw_sextic_radical_code_relation
    encoded_monic_sextic_radicalb)).
exact: (FA.encoded_raw_sextic_radical_code_relation_murec
  ra_encoded_monic_sextic_radical_correct).
Qed.

Theorem encoded_raw_sextic_radicalb_mathcomp values :
  encoded_raw_sextic_radicalb values =
  SD.coefficient_sextic_radicalb
    (FA.IF.decode_sextic_coefficients values).
Proof.
exact: (FA.encoded_raw_sextic_radicalb_mathcomp
  encoded_monic_sextic_radical_exact).
Qed.

Theorem encoded_raw_sextic_radicalP values :
  reflect
    (SD.all_roots_radical_coefficients
      (FA.IF.decode_sextic_coefficients values))
    (encoded_raw_sextic_radicalb values).
Proof.
exact: (FA.encoded_raw_sextic_radicalP
  encoded_monic_sextic_radical_exact).
Qed.

Theorem encoded_raw_sextic_radical_codeP code :
  reflect
    (SD.all_roots_radical_coefficients
      (FA.IF.decode_sextic_coefficients (project 7 code)))
    (encoded_raw_sextic_radical_codeb code).
Proof.
exact: encoded_raw_sextic_radicalP.
Qed.

Lemma encoded_raw_sextic_radical_relation_mathcomp values out :
  encoded_raw_sextic_radical_relation values out <->
  out = bool_to_nat
    (SD.coefficient_sextic_radicalb
      (FA.IF.decode_sextic_coefficients values)).
Proof.
rewrite /encoded_raw_sextic_radical_relation
  encoded_raw_sextic_radicalb_mathcomp.
reflexivity.
Qed.

Lemma encoded_raw_sextic_radical_code_relation_mathcomp code out :
  encoded_raw_sextic_radical_code_relation (code ## vec_nil) out <->
  out = bool_to_nat
    (SD.coefficient_sextic_radicalb
      (FA.IF.decode_sextic_coefficients (project 7 code))).
Proof.
rewrite /encoded_raw_sextic_radical_code_relation
  /encoded_raw_sextic_radical_codeb.
cbn [vec_head].
rewrite encoded_raw_sextic_radicalb_mathcomp.
reflexivity.
Qed.

End CoreAssembly.

End PolynomialFormulasSexticMuRecCompleteDecision.

Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.ra_encoded_monic_sextic_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_monic_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_monic_sextic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_monic_sextic_radicalb_mathcomp.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_monic_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.ra_encoded_raw_sextic_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_raw_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_raw_sextic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_raw_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecCompleteDecision.encoded_raw_sextic_radical_codeP.
