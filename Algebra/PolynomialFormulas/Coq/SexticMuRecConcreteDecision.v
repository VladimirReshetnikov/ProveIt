(* ===================================================================== *)
(*  Concrete Mu-recursive cores for the complete sextic decision.        *)
(*                                                                       *)
(*  The collision and rational-root programs are fixed here.  Their      *)
(*  semantic exactness remains an explicit proof package, so the exact   *)
(*  evaluator bridges can be connected without changing the assembly.   *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia Vector.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From PolynomialFormulas Require Import
  AbelRuffini SexticRecursiveCore SexticMuRecComputability
  SexticMuRecFactorDecision SexticMuRecCollisionEvaluator
  SexticMuRecResolventRootEvaluator SexticMuRecSeparatingInstance
  SexticMuRecIrreducibleAssembly SexticMuRecSemanticDecision
  SexticMuRecCompleteDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecConcreteDecision.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.
Module MSI := PolynomialFormulasSexticMuRecSeparatingInstance.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module CD := PolynomialFormulasSexticMuRecCompleteDecision.
Module SD := PolynomialFormulasSexticMuRecSemanticDecision.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* --------------------------------------------------------------------- *)
(* Every six-vector is the canonical code of a monic coefficient tuple. *)

Definition decode_monic_sextic_coefficients
    (values : Vector.t nat 6) : SRC.monic_sextic :=
  [tuple
    mathcomp_zigzag_decode (vec_pos values pos0);
    mathcomp_zigzag_decode (vec_pos values pos1);
    mathcomp_zigzag_decode (vec_pos values pos2);
    mathcomp_zigzag_decode (vec_pos values pos3);
    mathcomp_zigzag_decode (vec_pos values pos4);
    mathcomp_zigzag_decode (vec_pos values pos5)].

Lemma mathcomp_zigzag_encode_decode code :
  mathcomp_zigzag_encode (mathcomp_zigzag_decode code) = code.
Proof.
destruct (Nat.Even_or_Odd code) as [[magnitude ->]|[magnitude ->]].
- rewrite /mathcomp_zigzag_decode
    zigzag_positive_even zigzag_negative_even subr0.
  reflexivity.
- rewrite /mathcomp_zigzag_decode
    zigzag_positive_odd zigzag_negative_odd sub0r -NegzE.
  reflexivity.
Qed.

Lemma decode_encode_monic_sextic_coefficients f :
  decode_monic_sextic_coefficients
      (FD.encode_monic_sextic_coefficients f) = f.
Proof.
rewrite /decode_monic_sextic_coefficients
  /FD.encode_monic_sextic_coefficients.
apply: eq_from_tnth=> i.
rewrite !(@tnth_nth 6 int 0).
case: i=> [[|[|[|[|[|[|i]]]]]] hi] //=;
  rewrite mathcomp_zigzag_decode_encode //.
Qed.

Lemma encode_decode_monic_sextic_coefficients values :
  FD.encode_monic_sextic_coefficients
      (decode_monic_sextic_coefficients values) = values.
Proof.
rewrite /FD.encode_monic_sextic_coefficients
  /decode_monic_sextic_coefficients.
apply vec_pos_ext=> variable.
analyse pos variable; cbn [vec_pos pos_S_inv];
  rewrite mathcomp_zigzag_encode_decode //.
Qed.

(* --------------------------------------------------------------------- *)
(* Boolean views of the collision indicators and their checked programs. *)

Definition pair_collision_core (values : Vector.t nat 8) : bool :=
  Nat.eqb (CE.encoded_pair_collision_test values) 1.

Definition triple_collision_core (values : Vector.t nat 8) : bool :=
  Nat.eqb (CE.encoded_triple_collision_test values) 1.

Definition pair_collision_program : recalg 8 :=
  CE.ra_pair_collision_test.

Definition triple_collision_program : recalg 8 :=
  CE.ra_triple_collision_test.

Lemma encoded_pair_collision_test_bool values :
  CE.encoded_pair_collision_test values =
  bool_to_nat (pair_collision_core values).
Proof.
unfold pair_collision_core, CE.encoded_pair_collision_test, ite_rel,
  bool_to_nat.
destruct (CE.encoded_pair_scaled_collision_value values); reflexivity.
Qed.

Lemma encoded_triple_collision_test_bool values :
  CE.encoded_triple_collision_test values =
  bool_to_nat (triple_collision_core values).
Proof.
unfold triple_collision_core, CE.encoded_triple_collision_test, ite_rel,
  bool_to_nat.
destruct (CE.encoded_triple_scaled_collision_value values); reflexivity.
Qed.

Theorem pair_collision_program_correct :
  IA.core_boolean_spec pair_collision_core pair_collision_program.
Proof.
intro values.
rewrite <- encoded_pair_collision_test_bool.
exact: CE.ra_pair_collision_test_correct.
Qed.

Theorem triple_collision_program_correct :
  IA.core_boolean_spec triple_collision_core triple_collision_program.
Proof.
intro values.
rewrite <- encoded_triple_collision_test_bool.
exact: CE.ra_triple_collision_test_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* The root evaluators already expose Booleans and Boolean correctness.  *)

Definition pair_root_core : Vector.t nat 8 -> bool :=
  RE.encoded_pair_resolvent_rootb.

Definition triple_root_core : Vector.t nat 8 -> bool :=
  RE.encoded_triple_resolvent_rootb.

Definition pair_root_program : recalg 8 :=
  RE.ra_pair_resolvent_root.

Definition triple_root_program : recalg 8 :=
  RE.ra_triple_resolvent_root.

Theorem pair_root_program_correct :
  IA.core_boolean_spec pair_root_core pair_root_program.
Proof. exact RE.ra_pair_resolvent_root_correct. Qed.

Theorem triple_root_program_correct :
  IA.core_boolean_spec triple_root_core triple_root_program.
Proof. exact RE.ra_triple_resolvent_root_correct. Qed.

(* --------------------------------------------------------------------- *)
(* Collision exactness supplies termination on all arbitrary code tuples. *)

Lemma pair_guarded_projected_eventually
    (Hcollision : IA.pair_collision_core_exact pair_collision_core) :
  IA.guarded_projected_eventually pair_collision_core.
Proof.
intro values.
pose f := decode_monic_sextic_coefficients values.
have Hroundtrip : FD.encode_monic_sextic_coefficients f = values.
  exact: encode_decode_monic_sextic_coefficients.
case hfactor: (SRC.has_bounded_proper_factor f).
- exists 0%N.
  rewrite -Hroundtrip /IA.guarded_projected_test
    /IA.encoded_factor_guard
    FD.encoded_monic_has_proper_factorb_mathcomp hfactor.
  reflexivity.
- have [index Hindex] := MSI.pair_projected_total_separates_eventually f.
  exists index.
  rewrite -Hroundtrip.
  rewrite (IA.pair_guarded_projected_test_mathcomp
    Hcollision index hfactor).
  exact Hindex.
Qed.

Lemma triple_guarded_projected_eventually
    (Hcollision : IA.triple_collision_core_exact triple_collision_core) :
  IA.guarded_projected_eventually triple_collision_core.
Proof.
intro values.
pose f := decode_monic_sextic_coefficients values.
have Hroundtrip : FD.encode_monic_sextic_coefficients f = values.
  exact: encode_decode_monic_sextic_coefficients.
case hfactor: (SRC.has_bounded_proper_factor f).
- exists 0%N.
  rewrite -Hroundtrip /IA.guarded_projected_test
    /IA.encoded_factor_guard
    FD.encoded_monic_has_proper_factorb_mathcomp hfactor.
  reflexivity.
- have [index Hindex] := MSI.triple_projected_total_separates_eventually f.
  exists index.
  rewrite -Hroundtrip.
  rewrite (IA.triple_guarded_projected_test_mathcomp
    Hcollision index hfactor).
  exact Hindex.
Qed.

(* --------------------------------------------------------------------- *)
(* One small proof package instantiates the complete generic assembly.    *)

Record core_semantic_exactness : Prop := {
  pair_collision_exact :
    IA.pair_collision_core_exact pair_collision_core;
  pair_root_exact :
    IA.pair_root_core_exact pair_root_core;
  triple_collision_exact :
    IA.triple_collision_core_exact triple_collision_core;
  triple_root_exact :
    IA.triple_root_core_exact triple_root_core
}.

Definition pair_eventually
    (exactness : core_semantic_exactness) :
  IA.guarded_projected_eventually pair_collision_core :=
  pair_guarded_projected_eventually (pair_collision_exact exactness).

Definition triple_eventually
    (exactness : core_semantic_exactness) :
  IA.guarded_projected_eventually triple_collision_core :=
  triple_guarded_projected_eventually (triple_collision_exact exactness).

Definition encoded_monic_sextic_radicalb
    (exactness : core_semantic_exactness)
    (values : Vector.t nat 6) : bool :=
  @CD.encoded_monic_sextic_radicalb
    pair_collision_core pair_root_core (pair_eventually exactness)
    triple_collision_core triple_root_core (triple_eventually exactness)
    values.

Definition ra_encoded_monic_sextic_radical : recalg 6 :=
  CD.ra_encoded_monic_sextic_radical
    pair_collision_program pair_root_program
    triple_collision_program triple_root_program.

Lemma ra_encoded_monic_sextic_radical_correct
    (exactness : core_semantic_exactness) values :
  ⟦ra_encoded_monic_sextic_radical⟧ values
    (bool_to_nat (encoded_monic_sextic_radicalb exactness values)).
Proof.
exact: (CD.ra_encoded_monic_sextic_radical_correct
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Definition encoded_monic_sextic_radical_relation
    (exactness : core_semantic_exactness)
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_sextic_radicalb exactness values).

Theorem encoded_monic_sextic_radical_relation_murec
    (exactness : core_semantic_exactness) :
  MuRec_computable (encoded_monic_sextic_radical_relation exactness).
Proof.
change (MuRec_computable
  (@CD.encoded_monic_sextic_radical_relation
    pair_collision_core pair_root_core (pair_eventually exactness)
    triple_collision_core triple_root_core (triple_eventually exactness))).
exact: (CD.encoded_monic_sextic_radical_relation_murec
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Theorem encoded_monic_sextic_radicalb_mathcomp
    (exactness : core_semantic_exactness) (f : SRC.monic_sextic) :
  encoded_monic_sextic_radicalb exactness
      (FD.encode_monic_sextic_coefficients f) =
  SD.projected_monic_sextic_radicalb f.
Proof.
exact: (CD.encoded_monic_sextic_radicalb_mathcomp
  (pair_eventually exactness) (triple_eventually exactness)
  (pair_collision_exact exactness) (pair_root_exact exactness)
  (triple_collision_exact exactness) (triple_root_exact exactness)).
Qed.

Theorem encoded_monic_sextic_radicalP
    (exactness : core_semantic_exactness) (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves
      (CD.SRD.rational_monic_sextic f))
    (encoded_monic_sextic_radicalb exactness
      (FD.encode_monic_sextic_coefficients f)).
Proof.
exact: (CD.encoded_monic_sextic_radicalP
  (pair_eventually exactness) (triple_eventually exactness)
  (pair_collision_exact exactness) (pair_root_exact exactness)
  (triple_collision_exact exactness) (triple_root_exact exactness)).
Qed.

(* --------------------------------------------------------------------- *)
(* Public raw seven-vector and one-natural specializations.               *)

Definition encoded_raw_sextic_radicalb
    (exactness : core_semantic_exactness)
    (values : Vector.t nat 7) : bool :=
  @CD.encoded_raw_sextic_radicalb
    pair_collision_core pair_root_core (pair_eventually exactness)
    triple_collision_core triple_root_core (triple_eventually exactness)
    values.

Definition ra_encoded_raw_sextic_radical : recalg 7 :=
  CD.ra_encoded_raw_sextic_radical
    pair_collision_program pair_root_program
    triple_collision_program triple_root_program.

Lemma ra_encoded_raw_sextic_radical_correct
    (exactness : core_semantic_exactness) values :
  ⟦ra_encoded_raw_sextic_radical⟧ values
    (bool_to_nat (encoded_raw_sextic_radicalb exactness values)).
Proof.
exact: (CD.ra_encoded_raw_sextic_radical_correct
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Definition encoded_raw_sextic_radical_relation
    (exactness : core_semantic_exactness)
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (encoded_raw_sextic_radicalb exactness values).

Theorem encoded_raw_sextic_radical_relation_murec
    (exactness : core_semantic_exactness) :
  MuRec_computable (encoded_raw_sextic_radical_relation exactness).
Proof.
change (MuRec_computable
  (@CD.encoded_raw_sextic_radical_relation
    pair_collision_core pair_root_core (pair_eventually exactness)
    triple_collision_core triple_root_core (triple_eventually exactness))).
exact: (CD.encoded_raw_sextic_radical_relation_murec
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Definition encoded_raw_sextic_radical_codeb
    (exactness : core_semantic_exactness) (code : nat) : bool :=
  encoded_raw_sextic_radicalb exactness (project 7 code).

Definition ra_encoded_raw_sextic_radical_code : recalg 1 :=
  CD.ra_encoded_raw_sextic_radical_code
    pair_collision_program pair_root_program
    triple_collision_program triple_root_program.

Lemma ra_encoded_raw_sextic_radical_code_correct
    (exactness : core_semantic_exactness) code :
  ⟦ra_encoded_raw_sextic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat (encoded_raw_sextic_radical_codeb exactness code)).
Proof.
exact: (CD.ra_encoded_raw_sextic_radical_code_correct
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Definition encoded_raw_sextic_radical_code_relation
    (exactness : core_semantic_exactness)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_sextic_radical_codeb exactness (vec_head code)).

Theorem encoded_raw_sextic_radical_code_relation_murec
    (exactness : core_semantic_exactness) :
  MuRec_computable (encoded_raw_sextic_radical_code_relation exactness).
Proof.
change (MuRec_computable
  (@CD.encoded_raw_sextic_radical_code_relation
    pair_collision_core pair_root_core (pair_eventually exactness)
    triple_collision_core triple_root_core (triple_eventually exactness))).
exact: (CD.encoded_raw_sextic_radical_code_relation_murec
  pair_collision_program_correct pair_root_program_correct
  (pair_eventually exactness)
  triple_collision_program_correct triple_root_program_correct
  (triple_eventually exactness)).
Qed.

Theorem encoded_raw_sextic_radicalb_mathcomp
    (exactness : core_semantic_exactness) values :
  encoded_raw_sextic_radicalb exactness values =
  SD.coefficient_sextic_radicalb
    (CD.FA.IF.decode_sextic_coefficients values).
Proof.
exact: (CD.encoded_raw_sextic_radicalb_mathcomp
  (pair_eventually exactness) (triple_eventually exactness)
  (pair_collision_exact exactness) (pair_root_exact exactness)
  (triple_collision_exact exactness) (triple_root_exact exactness)).
Qed.

Theorem encoded_raw_sextic_radicalP
    (exactness : core_semantic_exactness) values :
  reflect
    (SD.all_roots_radical_coefficients
      (CD.FA.IF.decode_sextic_coefficients values))
    (encoded_raw_sextic_radicalb exactness values).
Proof.
exact: (CD.encoded_raw_sextic_radicalP
  (pair_eventually exactness) (triple_eventually exactness)
  (pair_collision_exact exactness) (pair_root_exact exactness)
  (triple_collision_exact exactness) (triple_root_exact exactness)).
Qed.

Theorem encoded_raw_sextic_radical_codeP
    (exactness : core_semantic_exactness) code :
  reflect
    (SD.all_roots_radical_coefficients
      (CD.FA.IF.decode_sextic_coefficients (project 7 code)))
    (encoded_raw_sextic_radical_codeb exactness code).
Proof.
exact: (CD.encoded_raw_sextic_radical_codeP
  (pair_eventually exactness) (triple_eventually exactness)
  (pair_collision_exact exactness) (pair_root_exact exactness)
  (triple_collision_exact exactness) (triple_root_exact exactness)).
Qed.

Lemma encoded_raw_sextic_radical_relation_mathcomp
    (exactness : core_semantic_exactness) values out :
  encoded_raw_sextic_radical_relation exactness values out <->
  out = bool_to_nat
    (SD.coefficient_sextic_radicalb
      (CD.FA.IF.decode_sextic_coefficients values)).
Proof.
rewrite /encoded_raw_sextic_radical_relation
  encoded_raw_sextic_radicalb_mathcomp.
reflexivity.
Qed.

Lemma encoded_raw_sextic_radical_code_relation_mathcomp
    (exactness : core_semantic_exactness) code out :
  encoded_raw_sextic_radical_code_relation
      exactness (code ## vec_nil) out <->
  out = bool_to_nat
    (SD.coefficient_sextic_radicalb
      (CD.FA.IF.decode_sextic_coefficients (project 7 code))).
Proof.
rewrite /encoded_raw_sextic_radical_code_relation
  /encoded_raw_sextic_radical_codeb.
cbn [vec_head].
rewrite encoded_raw_sextic_radicalb_mathcomp.
reflexivity.
Qed.

End PolynomialFormulasSexticMuRecConcreteDecision.

Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.decode_encode_monic_sextic_coefficients.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encode_decode_monic_sextic_coefficients.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.pair_collision_program_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.triple_collision_program_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.pair_guarded_projected_eventually.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.triple_guarded_projected_eventually.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.ra_encoded_monic_sextic_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_monic_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_monic_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.ra_encoded_raw_sextic_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_raw_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_raw_sextic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_raw_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecConcreteDecision.encoded_raw_sextic_radical_codeP.
