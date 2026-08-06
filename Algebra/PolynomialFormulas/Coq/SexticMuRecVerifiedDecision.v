(* ===================================================================== *)
(*  Fully verified concrete Mu-recursive sextic decision.                *)
(*                                                                       *)
(*  The closed core exactness theorem discharges the semantic package.   *)
(*  Every public Boolean, program, graph relation, and reflector below   *)
(*  is then free of semantic proof arguments.                            *)
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
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecSemanticDecision SexticMuRecIrreducibleAssembly
  SexticMuRecConcreteDecision SexticMuRecCoreExactness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecVerifiedDecision.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module SD := PolynomialFormulasSexticMuRecSemanticDecision.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module CC := PolynomialFormulasSexticMuRecConcreteDecision.
Module CX := PolynomialFormulasSexticMuRecCoreExactness.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* --------------------------------------------------------------------- *)
(* Closed exactness and the two certified terminating searches.          *)

Definition verified_core_semantic_exactness : CC.core_semantic_exactness :=
  CX.verified_core_semantic_exactness.

Definition pair_eventually :
  IA.guarded_projected_eventually CC.pair_collision_core :=
  CC.pair_eventually verified_core_semantic_exactness.

Definition triple_eventually :
  IA.guarded_projected_eventually CC.triple_collision_core :=
  CC.triple_eventually verified_core_semantic_exactness.

(* --------------------------------------------------------------------- *)
(* Six-vector monic decision.                                            *)

Definition encoded_monic_sextic_radicalb
    (values : Vector.t nat 6) : bool :=
  CC.encoded_monic_sextic_radicalb
    verified_core_semantic_exactness values.

Definition ra_encoded_monic_sextic_radical : recalg 6 :=
  CC.ra_encoded_monic_sextic_radical.

Lemma ra_encoded_monic_sextic_radical_correct values :
  ⟦ra_encoded_monic_sextic_radical⟧ values
    (bool_to_nat (encoded_monic_sextic_radicalb values)).
Proof.
exact: (CC.ra_encoded_monic_sextic_radical_correct
  verified_core_semantic_exactness).
Qed.

Definition encoded_monic_sextic_radical_relation
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_sextic_radicalb values).

Theorem encoded_monic_sextic_radical_relation_murec :
  MuRec_computable encoded_monic_sextic_radical_relation.
Proof.
exact: (CC.encoded_monic_sextic_radical_relation_murec
  verified_core_semantic_exactness).
Qed.

Theorem encoded_monic_sextic_radicalb_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_sextic_radicalb
      (FD.encode_monic_sextic_coefficients f) =
  SD.projected_monic_sextic_radicalb f.
Proof.
exact: (CC.encoded_monic_sextic_radicalb_mathcomp
  verified_core_semantic_exactness).
Qed.

Theorem encoded_monic_sextic_radical_canonicalP
    (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (encoded_monic_sextic_radicalb
      (FD.encode_monic_sextic_coefficients f)).
Proof.
exact: (CC.encoded_monic_sextic_radicalP
  verified_core_semantic_exactness).
Qed.

Theorem encoded_monic_sextic_radicalP values :
  reflect
    (radical_formula_solves
      (SRD.rational_monic_sextic
        (CC.decode_monic_sextic_coefficients values)))
    (encoded_monic_sextic_radicalb values).
Proof.
have H := CC.encoded_monic_sextic_radicalP
  verified_core_semantic_exactness
  (CC.decode_monic_sextic_coefficients values).
rewrite CC.encode_decode_monic_sextic_coefficients in H.
exact H.
Qed.

Definition encoded_monic_sextic_radical_decidable values :
  {radical_formula_solves
    (SRD.rational_monic_sextic
      (CC.decode_monic_sextic_coefficients values))} +
  {~ radical_formula_solves
    (SRD.rational_monic_sextic
      (CC.decode_monic_sextic_coefficients values))}.
Proof.
case: (encoded_monic_sextic_radicalP values)=> H.
- left; exact H.
- right; exact H.
Defined.

(* --------------------------------------------------------------------- *)
(* One-natural monic decision.                                           *)

Definition encoded_monic_sextic_radical_codeb (code : nat) : bool :=
  encoded_monic_sextic_radicalb (project 6 code).

Definition ra_encoded_monic_sextic_radical_code : recalg 1 :=
  ra_comp ra_encoded_monic_sextic_radical (ra_vec_project 6).

Lemma ra_encoded_monic_sextic_radical_code_correct code :
  ⟦ra_encoded_monic_sextic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat (encoded_monic_sextic_radical_codeb code)).
Proof.
unfold ra_encoded_monic_sextic_radical_code,
  encoded_monic_sextic_radical_codeb.
exists (project 6 code); split.
- exact: ra_encoded_monic_sextic_radical_correct.
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_sextic_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_sextic_radical_codeb (vec_head code)).

Theorem encoded_monic_sextic_radical_code_relation_murec :
  MuRec_computable encoded_monic_sextic_radical_code_relation.
Proof.
unfold encoded_monic_sextic_radical_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_monic_sextic_radical_codeb (vec_head code)))
  ra_encoded_monic_sextic_radical_code _).
intro values; vec split values with code; vec nil values.
exact: ra_encoded_monic_sextic_radical_code_correct.
Qed.

Theorem encoded_monic_sextic_radical_codeP code :
  reflect
    (radical_formula_solves
      (SRD.rational_monic_sextic
        (CC.decode_monic_sextic_coefficients (project 6 code))))
    (encoded_monic_sextic_radical_codeb code).
Proof. exact: encoded_monic_sextic_radicalP. Qed.

Definition encoded_monic_sextic_radical_code_decidable code :
  {radical_formula_solves
    (SRD.rational_monic_sextic
      (CC.decode_monic_sextic_coefficients (project 6 code)))} +
  {~ radical_formula_solves
    (SRD.rational_monic_sextic
      (CC.decode_monic_sextic_coefficients (project 6 code)))}.
Proof.
case: (encoded_monic_sextic_radical_codeP code)=> H.
- left; exact H.
- right; exact H.
Defined.

(* --------------------------------------------------------------------- *)
(* Seven-vector raw coefficient decision.                               *)

Definition encoded_raw_sextic_radicalb
    (values : Vector.t nat 7) : bool :=
  CC.encoded_raw_sextic_radicalb
    verified_core_semantic_exactness values.

Definition ra_encoded_raw_sextic_radical : recalg 7 :=
  CC.ra_encoded_raw_sextic_radical.

Lemma ra_encoded_raw_sextic_radical_correct values :
  ⟦ra_encoded_raw_sextic_radical⟧ values
    (bool_to_nat (encoded_raw_sextic_radicalb values)).
Proof.
exact: (CC.ra_encoded_raw_sextic_radical_correct
  verified_core_semantic_exactness).
Qed.

Definition encoded_raw_sextic_radical_relation
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (encoded_raw_sextic_radicalb values).

Theorem encoded_raw_sextic_radical_relation_murec :
  MuRec_computable encoded_raw_sextic_radical_relation.
Proof.
exact: (CC.encoded_raw_sextic_radical_relation_murec
  verified_core_semantic_exactness).
Qed.

Theorem encoded_raw_sextic_radicalb_mathcomp values :
  encoded_raw_sextic_radicalb values =
  SD.coefficient_sextic_radicalb
    (CC.CD.FA.IF.decode_sextic_coefficients values).
Proof.
exact: (CC.encoded_raw_sextic_radicalb_mathcomp
  verified_core_semantic_exactness).
Qed.

Theorem encoded_raw_sextic_radicalP values :
  reflect
    (SD.all_roots_radical_coefficients
      (CC.CD.FA.IF.decode_sextic_coefficients values))
    (encoded_raw_sextic_radicalb values).
Proof.
exact: (CC.encoded_raw_sextic_radicalP
  verified_core_semantic_exactness).
Qed.

Definition encoded_raw_sextic_radical_decidable values :
  {SD.all_roots_radical_coefficients
    (CC.CD.FA.IF.decode_sextic_coefficients values)} +
  {~ SD.all_roots_radical_coefficients
    (CC.CD.FA.IF.decode_sextic_coefficients values)}.
Proof.
case: (encoded_raw_sextic_radicalP values)=> H.
- left; exact H.
- right; exact H.
Defined.

(* --------------------------------------------------------------------- *)
(* One-natural raw coefficient decision.                                *)

Definition encoded_raw_sextic_radical_codeb (code : nat) : bool :=
  CC.encoded_raw_sextic_radical_codeb
    verified_core_semantic_exactness code.

Definition ra_encoded_raw_sextic_radical_code : recalg 1 :=
  CC.ra_encoded_raw_sextic_radical_code.

Lemma ra_encoded_raw_sextic_radical_code_correct code :
  ⟦ra_encoded_raw_sextic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat (encoded_raw_sextic_radical_codeb code)).
Proof.
exact: (CC.ra_encoded_raw_sextic_radical_code_correct
  verified_core_semantic_exactness).
Qed.

Definition encoded_raw_sextic_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_sextic_radical_codeb (vec_head code)).

Theorem encoded_raw_sextic_radical_code_relation_murec :
  MuRec_computable encoded_raw_sextic_radical_code_relation.
Proof.
exact: (CC.encoded_raw_sextic_radical_code_relation_murec
  verified_core_semantic_exactness).
Qed.

Theorem encoded_raw_sextic_radical_codeP code :
  reflect
    (SD.all_roots_radical_coefficients
      (CC.CD.FA.IF.decode_sextic_coefficients (project 7 code)))
    (encoded_raw_sextic_radical_codeb code).
Proof.
exact: (CC.encoded_raw_sextic_radical_codeP
  verified_core_semantic_exactness).
Qed.

Definition encoded_raw_sextic_radical_code_decidable code :
  {SD.all_roots_radical_coefficients
    (CC.CD.FA.IF.decode_sextic_coefficients (project 7 code))} +
  {~ SD.all_roots_radical_coefficients
    (CC.CD.FA.IF.decode_sextic_coefficients (project 7 code))}.
Proof.
case: (encoded_raw_sextic_radical_codeP code)=> H.
- left; exact H.
- right; exact H.
Defined.

End PolynomialFormulasSexticMuRecVerifiedDecision.

Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.verified_core_semantic_exactness.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_decidable.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_code_decidable.
