(* ===================================================================== *)
(*  Final composition layer for the concrete Mu-recursive sextic code.   *)
(*                                                                       *)
(*  The reducible monic branch is fully instantiated below.  The raw     *)
(*  seven-coefficient front end is deliberately generic in the exact     *)
(*  monic decision, so the irreducible collision search can be attached  *)
(*  without changing any of the coefficient plumbing proved here.        *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Vector.
From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.
From PolynomialFormulas Require Import
  AbelRuffini QuinticCanonicalDecision SexticRecursiveCore
  SexticArithmeticFactorSearch SexticReducibleDecision
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecQuinticBranch SexticMuRecQuinticResolvent
  SexticMuRecReducibleSemantics SexticMuRecIntegerFrontEnd
  SexticMuRecSemanticDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecFinalAssembly.

Module QCD := PolynomialFormulasQuinticCanonicalDecision.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SAF := PolynomialFormulasSexticArithmeticFactorSearch.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module QB := PolynomialFormulasSexticMuRecQuinticBranch.
Module QR := PolynomialFormulasSexticMuRecQuinticResolvent.
Module RS := PolynomialFormulasSexticMuRecReducibleSemantics.
Module IF := PolynomialFormulasSexticMuRecIntegerFrontEnd.
Module SD := PolynomialFormulasSexticMuRecSemanticDecision.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* --------------------------------------------------------------------- *)
(* Reusable Boolean composition inside the recursive-algebra model.      *)

(** [ra_boolean_if guard when_true when_false] evaluates all three
    programs on the same input.  Since Booleans are represented by
    [0] and [1], [ra_ite] receives the false arm before the true arm. *)
Definition ra_boolean_if {arity}
    (guard when_true when_false : recalg arity) : recalg arity :=
  ra_comp ra_ite
    (guard ## when_false ## when_true ## vec_nil).

Lemma ite_rel_bool guard when_true when_false :
  ite_rel (bool_to_nat guard)
    (bool_to_nat when_false) (bool_to_nat when_true) =
  bool_to_nat (if guard then when_true else when_false).
Proof. by case: guard; case: when_true; case: when_false. Qed.

Lemma ra_boolean_if_correct {arity}
    (guard_program when_true_program when_false_program : recalg arity)
    (guard when_true when_false : Vector.t nat arity -> bool)
    (guard_correct : forall values,
      ⟦guard_program⟧ values (bool_to_nat (guard values)))
    (when_true_correct : forall values,
      ⟦when_true_program⟧ values (bool_to_nat (when_true values)))
    (when_false_correct : forall values,
      ⟦when_false_program⟧ values (bool_to_nat (when_false values)))
    values :
  ⟦ra_boolean_if guard_program when_true_program when_false_program⟧
    values
    (bool_to_nat
      (if guard values then when_true values else when_false values)).
Proof.
rewrite /ra_boolean_if -ite_rel_bool.
eapply ra_comp3_val.
- exact: guard_correct.
- exact: when_false_correct.
- exact: when_true_correct.
- exact: ra_ite_val.
Qed.

Definition boolean_if_relation {arity}
    (guard when_true when_false : Vector.t nat arity -> bool)
    (values : Vector.t nat arity) (out : nat) : Prop :=
  out = bool_to_nat
    (if guard values then when_true values else when_false values).

Theorem boolean_if_relation_murec {arity}
    (guard_program when_true_program when_false_program : recalg arity)
    (guard when_true when_false : Vector.t nat arity -> bool)
    (guard_correct : forall values,
      ⟦guard_program⟧ values (bool_to_nat (guard values)))
    (when_true_correct : forall values,
      ⟦when_true_program⟧ values (bool_to_nat (when_true values)))
    (when_false_correct : forall values,
      ⟦when_false_program⟧ values (bool_to_nat (when_false values))) :
  MuRec_computable (boolean_if_relation guard when_true when_false).
Proof.
unfold boolean_if_relation.
refine (@recalg_graph_murec arity
  (fun values => bool_to_nat
    (if guard values then when_true values else when_false values))
  (ra_boolean_if guard_program when_true_program when_false_program) _).
exact (ra_boolean_if_correct guard_correct
  when_true_correct when_false_correct).
Qed.

(** Boolean disjunction is the specialized conditional
    [if left then true else right]. *)
Definition ra_boolean_or {arity}
    (left right : recalg arity) : recalg arity :=
  ra_boolean_if left (ra_cst_n arity 1) right.

Lemma bool_to_nat_orb left right :
  bool_to_nat (left || right) =
  bool_to_nat (if left then true else right).
Proof. by case: left; case: right. Qed.

Lemma ra_boolean_or_correct {arity}
    (left_program right_program : recalg arity)
    (left right : Vector.t nat arity -> bool)
    (left_correct : forall values,
      ⟦left_program⟧ values (bool_to_nat (left values)))
    (right_correct : forall values,
      ⟦right_program⟧ values (bool_to_nat (right values)))
    values :
  ⟦ra_boolean_or left_program right_program⟧ values
    (bool_to_nat (left values || right values)).
Proof.
rewrite bool_to_nat_orb.
eapply (@ra_boolean_if_correct arity
  left_program (ra_cst_n arity 1) right_program
  left (fun _ => true) right).
- exact: left_correct.
- exact: (fun input => ra_cst_n_val 1 input).
- exact: right_correct.
Qed.

Definition boolean_or_relation {arity}
    (left right : Vector.t nat arity -> bool)
    (values : Vector.t nat arity) (out : nat) : Prop :=
  out = bool_to_nat (left values || right values).

Theorem boolean_or_relation_murec {arity}
    (left_program right_program : recalg arity)
    (left right : Vector.t nat arity -> bool)
    (left_correct : forall values,
      ⟦left_program⟧ values (bool_to_nat (left values)))
    (right_correct : forall values,
      ⟦right_program⟧ values (bool_to_nat (right values))) :
  MuRec_computable (boolean_or_relation left right).
Proof.
unfold boolean_or_relation.
refine (@recalg_graph_murec arity
  (fun values => bool_to_nat (left values || right values))
  (ra_boolean_or left_program right_program) _).
exact (ra_boolean_or_correct left_correct right_correct).
Qed.

(* --------------------------------------------------------------------- *)
(* The exact concrete reducible monic sextic dispatcher.                 *)

Lemma ra_encoded_monic_has_linear_factor_correct values :
  ⟦ra_encoded_monic_has_linear_factor⟧ values
    (bool_to_nat (encoded_monic_has_linear_factorb values)).
Proof.
unfold ra_encoded_monic_has_linear_factor.
rewrite -encoded_monic_has_linear_factor_indicator.
exact: compile_nat_expression_correct.
Qed.

Lemma ra_encoded_monic_has_proper_factor_correct values :
  ⟦ra_encoded_monic_has_proper_factor⟧ values
    (bool_to_nat (encoded_monic_has_proper_factorb values)).
Proof.
unfold ra_encoded_monic_has_proper_factor.
rewrite -encoded_monic_has_proper_factor_indicator.
exact: compile_nat_expression_correct.
Qed.

(** On canonical encodings, the concrete quintic program satisfies the
    exact contract expected by the reducible sextic semantics. *)
Lemma encoded_quintic_radical_correct_QCD :
  RS.encoded_quintic_radical_correct
    QR.encoded_monic_quintic_radicalb.
Proof.
intro q.
change (reflect
  (radical_formula_solves (QCD.rational_monic_quintic q))
  (QR.encoded_monic_quintic_radicalb
    (QB.encode_monic_quintic_coefficients q))).
have hencode :
    QB.encode_monic_quintic_coefficients q =
    QR.encode_monic_quintic q by reflexivity.
rewrite hencode QR.encoded_monic_quintic_radicalb_QCD.
exact: QCD.quintic_radicalP.
Qed.

Lemma encoded_quintic_radical_decision_QCD q :
  RS.encoded_quintic_radical_decision
      QR.encoded_monic_quintic_radicalb q =
  QCD.quintic_radicalb q.
Proof.
rewrite /RS.encoded_quintic_radical_decision.
change
  (QR.encoded_monic_quintic_radicalb
    (QR.encode_monic_quintic q) = QCD.quintic_radicalb q).
exact: QR.encoded_monic_quintic_radicalb_QCD.
Qed.

(** If a linear factor exists, inspect every exact linear quotient with
    the concrete quintic decision.  Otherwise the proper-factor Boolean
    is precisely the quadratic/cubic branch, whose answer is positive. *)
Definition encoded_monic_reducible_radicalb
    (values : Vector.t nat 6) : bool :=
  if encoded_monic_has_linear_factorb values
  then QB.encoded_monic_reducible_linear_branchb
    QR.encoded_monic_quintic_radicalb values
  else encoded_monic_has_proper_factorb values.

Definition ra_encoded_monic_reducible_radical : recalg 6 :=
  ra_boolean_if
    ra_encoded_monic_has_linear_factor
    (QB.ra_encoded_monic_reducible_linear_branch
      QR.ra_encoded_monic_quintic_radical)
    ra_encoded_monic_has_proper_factor.

Lemma ra_encoded_monic_reducible_radical_correct values :
  ⟦ra_encoded_monic_reducible_radical⟧ values
    (bool_to_nat (encoded_monic_reducible_radicalb values)).
Proof.
unfold ra_encoded_monic_reducible_radical,
  encoded_monic_reducible_radicalb.
apply (ra_boolean_if_correct
  ra_encoded_monic_has_linear_factor_correct
  (QB.ra_encoded_monic_reducible_linear_branch_correct
    QR.ra_encoded_monic_quintic_radical_correct)
  ra_encoded_monic_has_proper_factor_correct).
Qed.

Definition encoded_monic_reducible_radical_relation
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_reducible_radicalb values).

Theorem encoded_monic_reducible_radical_relation_murec :
  MuRec_computable encoded_monic_reducible_radical_relation.
Proof.
unfold encoded_monic_reducible_radical_relation.
refine (@recalg_graph_murec 6
  (fun values => bool_to_nat (encoded_monic_reducible_radicalb values))
  ra_encoded_monic_reducible_radical _).
exact: ra_encoded_monic_reducible_radical_correct.
Qed.

Lemma encoded_monic_has_linear_factorb_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_has_linear_factorb
      (FD.encode_monic_sextic_coefficients f) =
  SRC.has_bounded_linear_factor f.
Proof.
apply Bool.eq_true_iff_eq.
rewrite encoded_monic_has_linear_factorb_true_iff
  FD.encoded_monic_linear_factor_mathcomp_iff
  SAF.has_arithmetic_linear_factorE.
reflexivity.
Qed.

Theorem encoded_monic_reducible_radicalb_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_reducible_radicalb
      (FD.encode_monic_sextic_coefficients f) =
  RS.bounded_search_reducible_sextic_radical_branch
    QR.encoded_monic_quintic_radicalb f.
Proof.
rewrite /encoded_monic_reducible_radicalb
  /RS.bounded_search_reducible_sextic_radical_branch
  encoded_monic_has_linear_factorb_mathcomp.
case hlinear: (SRC.has_bounded_linear_factor f).
- exact: QB.encoded_monic_reducible_linear_branchb_mathcomp.
- rewrite FD.encoded_monic_has_proper_factorb_mathcomp
    /SRC.has_bounded_proper_factor hlinear.
  reflexivity.
Qed.

Theorem encoded_monic_reducible_radicalb_selected
    (f : SRC.monic_sextic) :
  encoded_monic_reducible_radicalb
      (FD.encode_monic_sextic_coefficients f) =
  SRD.reducible_sextic_radical_branch QCD.quintic_radicalb f.
Proof.
rewrite encoded_monic_reducible_radicalb_mathcomp.
rewrite (RS.bounded_search_reducible_sextic_radical_branch_selected
  encoded_quintic_radical_correct_QCD).
rewrite /SRD.reducible_sextic_radical_branch
  /SRD.selected_linear_radical_branch.
case: (SRC.has_bounded_linear_factor f)=> //=.
exact: encoded_quintic_radical_decision_QCD.
Qed.

Theorem encoded_monic_reducible_radicalP
    (f : SRC.monic_sextic) :
  SRC.has_bounded_proper_factor f ->
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (encoded_monic_reducible_radicalb
      (FD.encode_monic_sextic_coefficients f)).
Proof.
move=> hproper.
rewrite encoded_monic_reducible_radicalb_mathcomp.
exact: (RS.bounded_search_reducible_sextic_radical_branchP
  encoded_quintic_radical_correct_QCD hproper).
Qed.

Lemma encoded_monic_reducible_radical_relation_mathcomp
    (f : SRC.monic_sextic) out :
  encoded_monic_reducible_radical_relation
      (FD.encode_monic_sextic_coefficients f) out <->
  out = bool_to_nat
    (SRD.reducible_sextic_radical_branch QCD.quintic_radicalb f).
Proof.
rewrite /encoded_monic_reducible_radical_relation
  encoded_monic_reducible_radicalb_selected.
reflexivity.
Qed.

Definition ra_encoded_monic_reducible_radical_code : recalg 1 :=
  ra_comp ra_encoded_monic_reducible_radical (ra_vec_project 6).

Lemma ra_encoded_monic_reducible_radical_code_correct code :
  ⟦ra_encoded_monic_reducible_radical_code⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_monic_reducible_radicalb (project 6 code))).
Proof.
unfold ra_encoded_monic_reducible_radical_code.
exists (project 6 code); split.
- exact: ra_encoded_monic_reducible_radical_correct.
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_reducible_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_reducible_radicalb
      (project 6 (vec_head code))).

Theorem encoded_monic_reducible_radical_code_relation_murec :
  MuRec_computable encoded_monic_reducible_radical_code_relation.
Proof.
unfold encoded_monic_reducible_radical_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_monic_reducible_radicalb
      (project 6 (vec_head code))))
  ra_encoded_monic_reducible_radical_code _).
intro values; vec split values with code; vec nil values.
exact: ra_encoded_monic_reducible_radical_code_correct.
Qed.

Lemma encoded_monic_reducible_radical_code_relation_mathcomp
    (f : SRC.monic_sextic) out :
  encoded_monic_reducible_radical_code_relation
      (inject (FD.encode_monic_sextic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat
    (SRD.reducible_sextic_radical_branch QCD.quintic_radicalb f).
Proof.
rewrite /encoded_monic_reducible_radical_code_relation.
cbn [vec_head].
rewrite project_inject encoded_monic_reducible_radicalb_selected.
reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Generic raw seven-coefficient front end.                              *)

(** A raw decision rejects a zero leading coefficient and otherwise
    runs its monic decision on the six coefficients produced by the
    proved integral monicization compiler. *)
Definition encoded_raw_sextic_radicalb
    (monic_decisionb : Vector.t nat 6 -> bool)
    (values : Vector.t nat 7) : bool :=
  if IF.encoded_raw_is_sexticb values
  then monic_decisionb (IF.encoded_monicization values)
  else false.

Definition ra_monicized_boolean
    (monic_decision : recalg 6) : recalg 7 :=
  ra_comp monic_decision IF.ra_monicization_components.

Lemma ra_monicized_boolean_correct
    (monic_decision : recalg 6)
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_decision_correct : forall coefficients,
      ⟦monic_decision⟧ coefficients
        (bool_to_nat (monic_decisionb coefficients))) values :
  ⟦ra_monicized_boolean monic_decision⟧ values
    (bool_to_nat
      (monic_decisionb (IF.encoded_monicization values))).
Proof.
unfold ra_monicized_boolean.
exists (IF.encoded_monicization values); split.
- exact: monic_decision_correct.
- intro variable; rewrite vec_pos_set.
  exact (IF.ra_monicization_component_correct variable values).
Qed.

Definition ra_encoded_raw_sextic_radical
    (monic_decision : recalg 6) : recalg 7 :=
  ra_boolean_if IF.ra_raw_is_sextic
    (ra_monicized_boolean monic_decision)
    (ra_cst_n 7 0).

Lemma ra_encoded_raw_sextic_radical_correct
    (monic_decision : recalg 6)
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_decision_correct : forall coefficients,
      ⟦monic_decision⟧ coefficients
        (bool_to_nat (monic_decisionb coefficients))) values :
  ⟦ra_encoded_raw_sextic_radical monic_decision⟧ values
    (bool_to_nat
      (encoded_raw_sextic_radicalb monic_decisionb values)).
Proof.
unfold ra_encoded_raw_sextic_radical,
  encoded_raw_sextic_radicalb.
eapply (@ra_boolean_if_correct 7
  IF.ra_raw_is_sextic
  (ra_monicized_boolean monic_decision)
  (ra_cst_n 7 0)
  IF.encoded_raw_is_sexticb
  (fun input => monic_decisionb (IF.encoded_monicization input))
  (fun _ => false)).
- exact: IF.ra_raw_is_sextic_correct.
- exact: (ra_monicized_boolean_correct monic_decision_correct).
- exact: (fun input => ra_cst_n_val 0 input).
Qed.

Definition encoded_raw_sextic_radical_relation
    (monic_decisionb : Vector.t nat 6 -> bool)
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_sextic_radicalb monic_decisionb values).

Theorem encoded_raw_sextic_radical_relation_murec
    (monic_decision : recalg 6)
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_decision_correct : forall coefficients,
      ⟦monic_decision⟧ coefficients
        (bool_to_nat (monic_decisionb coefficients))) :
  MuRec_computable
    (encoded_raw_sextic_radical_relation monic_decisionb).
Proof.
unfold encoded_raw_sextic_radical_relation.
refine (@recalg_graph_murec 7
  (fun values => bool_to_nat
    (encoded_raw_sextic_radicalb monic_decisionb values))
  (ra_encoded_raw_sextic_radical monic_decision) _).
exact (ra_encoded_raw_sextic_radical_correct monic_decision_correct).
Qed.

Definition ra_encoded_raw_sextic_radical_code
    (monic_decision : recalg 6) : recalg 1 :=
  ra_comp (ra_encoded_raw_sextic_radical monic_decision)
    (ra_vec_project 7).

Lemma ra_encoded_raw_sextic_radical_code_correct
    (monic_decision : recalg 6)
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_decision_correct : forall coefficients,
      ⟦monic_decision⟧ coefficients
        (bool_to_nat (monic_decisionb coefficients))) code :
  ⟦ra_encoded_raw_sextic_radical_code monic_decision⟧
    (code ## vec_nil)
    (bool_to_nat
      (encoded_raw_sextic_radicalb monic_decisionb
        (project 7 code))).
Proof.
unfold ra_encoded_raw_sextic_radical_code.
exists (project 7 code); split.
- exact (ra_encoded_raw_sextic_radical_correct
    monic_decision_correct (project 7 code)).
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_raw_sextic_radical_code_relation
    (monic_decisionb : Vector.t nat 6 -> bool)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_sextic_radicalb monic_decisionb
      (project 7 (vec_head code))).

Theorem encoded_raw_sextic_radical_code_relation_murec
    (monic_decision : recalg 6)
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_decision_correct : forall coefficients,
      ⟦monic_decision⟧ coefficients
        (bool_to_nat (monic_decisionb coefficients))) :
  MuRec_computable
    (encoded_raw_sextic_radical_code_relation monic_decisionb).
Proof.
unfold encoded_raw_sextic_radical_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_raw_sextic_radicalb monic_decisionb
      (project 7 (vec_head code))))
  (ra_encoded_raw_sextic_radical_code monic_decision) _).
intro values; vec split values with code; vec nil values.
exact (ra_encoded_raw_sextic_radical_code_correct
  monic_decision_correct code).
Qed.

(** Semantic contract needed from the eventual complete monic program.
    It is intentionally required only on canonical encodings. *)
Definition encoded_monic_sextic_radical_exact
    (monic_decisionb : Vector.t nat 6 -> bool) : Type :=
  forall f : SRC.monic_sextic,
    monic_decisionb (FD.encode_monic_sextic_coefficients f) =
    SD.projected_monic_sextic_radicalb f.

Theorem encoded_raw_sextic_radicalb_mathcomp
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_exact : encoded_monic_sextic_radical_exact monic_decisionb)
    values :
  encoded_raw_sextic_radicalb monic_decisionb values =
  SD.coefficient_sextic_radicalb (IF.decode_sextic_coefficients values).
Proof.
rewrite /encoded_raw_sextic_radicalb
  IF.encoded_raw_is_sexticb_mathcomp
  IF.encoded_monicization_mathcomp
  (monic_exact
    (SRC.monicize (IF.decode_sextic_coefficients values))).
rewrite /SD.coefficient_sextic_radicalb.
by case: (SRC.is_sexticb (IF.decode_sextic_coefficients values)).
Qed.

Theorem encoded_raw_sextic_radicalP
    (monic_decisionb : Vector.t nat 6 -> bool)
    (monic_exact : encoded_monic_sextic_radical_exact monic_decisionb)
    values :
  reflect
    (SD.all_roots_radical_coefficients
      (IF.decode_sextic_coefficients values))
    (encoded_raw_sextic_radicalb monic_decisionb values).
Proof.
rewrite (encoded_raw_sextic_radicalb_mathcomp monic_exact).
exact: SD.coefficient_sextic_radicalP.
Qed.

End PolynomialFormulasSexticMuRecFinalAssembly.

Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.boolean_if_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.boolean_or_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.ra_encoded_monic_reducible_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_monic_reducible_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_monic_reducible_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.ra_encoded_raw_sextic_radical_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_raw_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_raw_sextic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_monic_reducible_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecFinalAssembly.encoded_raw_sextic_radicalP.
