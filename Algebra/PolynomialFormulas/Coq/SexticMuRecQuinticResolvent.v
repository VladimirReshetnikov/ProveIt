(* ===================================================================== *)
(*  A fixed Mu-recursive compiler for the padded quintic resolvent.       *)
(*                                                                       *)
(*  The source is the seven-element sparse coefficient family from       *)
(*  [QuinticPaddedSymmetrization].  It is translated structurally into    *)
(*  the signed-expression language whose compiler is proved correct in   *)
(*  [SexticMuRecComputability].                                          *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.

From Undecidability.Shared.Libs.DLW Require Import utils_nat pos vec.
From Undecidability.MuRec.Util Require Import
  recalg ra_utils recomp ra_recomp.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticSparsePolynomials
  SexticNewtonPowerSums SexticComputedResolvents
  SexticRecursiveCore SexticRationalRootSearch SexticHomogeneousRootSearch
  QuinticRecursiveFactor QuinticThetaValues QuinticGaloisAction
  QuinticPaddedSymmetrization QuinticCanonicalDecision
  SexticMuRecQuinticBranch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecQuinticResolvent.

Module SP := PolynomialFormulasSexticSparsePolynomials.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module SCR := PolynomialFormulasSexticComputedResolvents.
Module SRR := PolynomialFormulasSexticRationalRootSearch.
Module SHR := PolynomialFormulasSexticHomogeneousRootSearch.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QTV := PolynomialFormulasQuinticThetaValues.
Module QGA := PolynomialFormulasQuinticGaloisAction.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module QCD := PolynomialFormulasQuinticCanonicalDecision.
Module QB := PolynomialFormulasSexticMuRecQuinticBranch.

(* --------------------------------------------------------------------- *)
(* Five zigzag codes denote the lower coefficients [f0,...,f4].          *)

Definition decode_monic_quintic
    (values : Vector.t nat 5) : QRF.monic_quintic :=
  [tuple
    mathcomp_zigzag_decode (vec_pos values pos0);
    mathcomp_zigzag_decode (vec_pos values pos1);
    mathcomp_zigzag_decode (vec_pos values pos2);
    mathcomp_zigzag_decode (vec_pos values pos3);
    mathcomp_zigzag_decode (vec_pos values pos4)].

Definition encode_monic_quintic
    (f : QRF.monic_quintic) : Vector.t nat 5 :=
  mathcomp_zigzag_encode f`_0 ##
  mathcomp_zigzag_encode f`_1 ##
  mathcomp_zigzag_encode f`_2 ##
  mathcomp_zigzag_encode f`_3 ##
  mathcomp_zigzag_encode f`_4 ## vec_nil.

Lemma decode_encode_monic_quintic f :
  decode_monic_quintic (encode_monic_quintic f) = f.
Proof.
  rewrite /decode_monic_quintic /encode_monic_quintic.
  apply: eq_from_tnth=> i.
  rewrite !(@tnth_nth 5 int 0).
  case: i=> [[|[|[|[|[|i]]]]] hi] //=;
    rewrite mathcomp_zigzag_decode_encode //.
Qed.

Definition quintic_vieta_values
    (values : Vector.t nat 5) : 6.-tuple int :=
  [tuple
    - mathcomp_zigzag_decode (vec_pos values pos4);
    mathcomp_zigzag_decode (vec_pos values pos3);
    - mathcomp_zigzag_decode (vec_pos values pos2);
    mathcomp_zigzag_decode (vec_pos values pos1);
    - mathcomp_zigzag_decode (vec_pos values pos0);
    0].

Lemma quintic_embedding_vieta_values values :
  SCR.monic_elementary_values
      (QRF.quintic_sextic_embedding (decode_monic_quintic values)) =
    quintic_vieta_values values.
Proof.
  rewrite /SCR.monic_elementary_values /quintic_vieta_values.
  apply: eq_from_tnth=> i.
  rewrite !(@tnth_nth 6 int 0).
  case: i=> [[|[|[|[|[|[|i]]]]]] hi] //=.
  all: rewrite (QRF.quintic_sextic_embedding_nthE
    (decode_monic_quintic values)) //=.
  all: rewrite /decode_monic_quintic /=.
Qed.

(* --------------------------------------------------------------------- *)
(* Structural translation of sparse integer polynomials.                 *)

Definition signed_int_constant {arity : nat}
    (coefficient : int) : signed_expression arity :=
  match coefficient with
  | Posz magnitude => signed_of_nat_expression (NatConst magnitude)
  | Negz magnitude =>
      signed_negate
        (signed_of_nat_expression (NatConst magnitude.+1))
  end.

Lemma eval_mathcomp_signed_int_constant {arity} coefficient
    (values : Vector.t nat arity) :
  eval_mathcomp_signed_expression (signed_int_constant coefficient) values =
    coefficient.
Proof.
  case: coefficient=> magnitude.
  - exact: eval_mathcomp_signed_of_nat_expression.
  - rewrite /signed_int_constant eval_mathcomp_signed_negate
      eval_mathcomp_signed_of_nat_expression.
    exact: esym (NegzE magnitude).
Qed.

(** The six Vieta coordinates of [X * f] are
    [-f4,f3,-f2,f1,-f0,0]. *)
Definition quintic_sparse_exponent_expression
    (exponent : SP.sparse_exponent) : signed_expression 5 :=
  signed_mult
    (signed_power (signed_negate (signed_coefficient pos4))
      (nth 0 exponent 0))
    (signed_mult
      (signed_power (signed_coefficient pos3) (nth 0 exponent 1))
      (signed_mult
        (signed_power (signed_negate (signed_coefficient pos2))
          (nth 0 exponent 2))
        (signed_mult
          (signed_power (signed_coefficient pos1) (nth 0 exponent 3))
          (signed_mult
            (signed_power (signed_negate (signed_coefficient pos0))
              (nth 0 exponent 4))
            (signed_power signed_zero (nth 0 exponent 5)))))).

Lemma eval_quintic_sparse_exponent_expression exponent values :
  eval_mathcomp_signed_expression
      (quintic_sparse_exponent_expression exponent) values =
    NPS.exponent_value_ring
      (SCR.monic_elementary_values
        (QRF.quintic_sextic_embedding (decode_monic_quintic values)))
      exponent.
Proof.
  rewrite /quintic_sparse_exponent_expression
    !eval_mathcomp_signed_mult !eval_mathcomp_signed_power
    !eval_mathcomp_signed_negate !eval_mathcomp_signed_coefficient
    eval_mathcomp_signed_of_nat_expression.
  rewrite quintic_embedding_vieta_values
    /NPS.exponent_value_ring !big_ord_recl !big_ord0.
  rewrite /quintic_vieta_values
    !(@tnth_nth 6 int 0) !(@tnth_nth 6 nat 0) /=.
  rewrite /bump /= mulr1.
  reflexivity.
Qed.

Definition quintic_sparse_term_expression
    (term : SP.sparse_term) : signed_expression 5 :=
  signed_mult (signed_int_constant term.1)
    (quintic_sparse_exponent_expression term.2).

Fixpoint quintic_sparse_polynomial_expression
    (polynomial : SP.sparse_polynomial) : signed_expression 5 :=
  match polynomial with
  | [::] => signed_zero
  | term :: polynomial' =>
      signed_plus (quintic_sparse_term_expression term)
        (quintic_sparse_polynomial_expression polynomial')
  end.

Lemma eval_quintic_sparse_polynomial_expression polynomial values :
  eval_mathcomp_signed_expression
      (quintic_sparse_polynomial_expression polynomial) values =
    NPS.sparse_eval_ring
      (SCR.monic_elementary_values
        (QRF.quintic_sextic_embedding (decode_monic_quintic values)))
      polynomial.
Proof.
  elim: polynomial=> [|[coefficient exponent] polynomial IH] /=.
  - rewrite eval_mathcomp_signed_of_nat_expression
      /NPS.sparse_eval_ring big_nil.
    reflexivity.
  - rewrite eval_mathcomp_signed_plus eval_mathcomp_signed_mult
      eval_mathcomp_signed_int_constant
      eval_quintic_sparse_exponent_expression IH
      /NPS.sparse_eval_ring big_cons intz.
    reflexivity.
Qed.

Definition quintic_resolvent_coefficient_expression
    (index : 'I_7) : signed_expression 5 :=
  quintic_sparse_polynomial_expression
    (QPS.symmetrized_weighted_quintic_coefficient index).

Theorem eval_quintic_resolvent_coefficient_expression index values :
  eval_mathcomp_signed_expression
      (quintic_resolvent_coefficient_expression index) values =
    QPS.quintic_scaled_resolvent_coefficient
      (decode_monic_quintic values) index.
Proof.
  exact: eval_quintic_sparse_polynomial_expression.
Qed.

(* --------------------------------------------------------------------- *)
(* Canonical zigzag output and the seven fixed coefficient programs.     *)

(** A signed expression stores a difference [positive - negative].  The
    following natural expression removes that non-canonical overlap and
    returns the ordinary even/odd zigzag code of the represented integer. *)
Definition signed_zigzag_code_expression {arity}
    (expression : signed_expression arity) : nat_expression arity :=
  let positive := signed_positive expression in
  let negative := signed_negative expression in
  let positive_difference := NatMinus positive negative in
  let negative_difference := NatMinus negative positive in
  NatIfZero negative_difference
    (NatMult (NatConst 2) positive_difference)
    (NatSucc
      (NatMult (NatConst 2)
        (NatMinus negative_difference (NatConst 1)))).

Lemma eval_signed_zigzag_code_expression {arity}
    (expression : signed_expression arity) values :
  eval_nat_expression (signed_zigzag_code_expression expression) values =
  mathcomp_zigzag_encode
    (eval_mathcomp_signed_expression expression values).
Proof.
  unfold signed_zigzag_code_expression,
    eval_mathcomp_signed_expression.
  cbn [eval_nat_expression].
  remember (eval_nat_expression (signed_positive expression) values)
    as positive eqn:Hpositive.
  remember (eval_nat_expression (signed_negative expression) values)
    as negative eqn:Hnegative.
  destruct (le_dec negative positive) as [Hle | Hnotle].
  - have Hzero : Nat.sub negative positive = 0%nat.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero.
    have Hdecomp :
        positive = Nat.add (Nat.sub positive negative) negative by lia.
    have Hint : (positive%:Z - negative%:Z : int) =
        Posz (Nat.sub positive negative).
    { by rewrite Hdecomp PoszD addrK Nat.add_sub. }
    rewrite Hint /mathcomp_zigzag_encode.
    reflexivity.
  - have Hlt : Nat.lt positive negative by lia.
    have Hposle : Nat.le positive negative by lia.
    have Hzero : Nat.sub positive negative = 0%nat.
    { apply Nat.sub_0_le. exact Hposle. }
    rewrite Hzero.
    have Hdiff : exists magnitude,
        Nat.sub negative positive = S magnitude.
    { have Hneq : Nat.sub negative positive <> 0%nat.
      { move=> Hzero'. apply Hnotle.
        exact: (proj1 (Nat.sub_0_le negative positive) Hzero'). }
      destruct (Nat.sub negative positive) as [|magnitude]
          eqn:Hdifference.
      - by exfalso; apply Hneq.
      - by exists magnitude. }
    destruct Hdiff as [magnitude Hdiff].
    rewrite Hdiff /=.
    have Hint : (positive%:Z - negative%:Z : int) = Negz magnitude.
    { have Hdecomp : negative = Nat.add positive (S magnitude) by lia.
      rewrite Hdecomp PoszD NegzE opprD addrA subrr add0r.
      reflexivity. }
    rewrite Hint /mathcomp_zigzag_encode.
    rewrite !Nat.sub_0_r !Nat.add_0_r.
    change (S (Nat.add magnitude magnitude) =
      Nat.add (Nat.mul 2 magnitude) 1).
    lia.
Qed.

Definition ordinal_of_pos {count} (variable : pos count) : 'I_count.
Proof.
  apply: Ordinal.
  apply/ltP.
  exact: (pos2nat_prop variable).
Defined.

Definition quintic_resolvent_coefficient_code_expression
    (index : 'I_7) : nat_expression 5 :=
  signed_zigzag_code_expression
    (quintic_resolvent_coefficient_expression index).

Definition ra_quintic_resolvent_coefficient
    (index : 'I_7) : recalg 5 :=
  compile_nat_expression
    (quintic_resolvent_coefficient_code_expression index).

Lemma ra_quintic_resolvent_coefficient_correct index values :
  ⟦ra_quintic_resolvent_coefficient index⟧ values
    (mathcomp_zigzag_encode
      (QPS.quintic_scaled_resolvent_coefficient
        (decode_monic_quintic values) index)).
Proof.
  rewrite /ra_quintic_resolvent_coefficient
    /quintic_resolvent_coefficient_code_expression.
  rewrite -eval_quintic_resolvent_coefficient_expression
    -eval_signed_zigzag_code_expression.
  exact: compile_nat_expression_correct.
Qed.

Definition quintic_resolvent_coefficients
    (f : QRF.monic_quintic) : Vector.t int 7 :=
  vec_set_pos (fun variable =>
    QPS.quintic_scaled_resolvent_coefficient f
      (ordinal_of_pos variable)).

Definition encoded_quintic_resolvent_coefficients
    (values : Vector.t nat 5) : Vector.t nat 7 :=
  vec_set_pos (fun variable =>
    eval_nat_expression
      (quintic_resolvent_coefficient_code_expression
        (ordinal_of_pos variable)) values).

Definition ra_quintic_resolvent_coefficients :
    Vector.t (recalg 5) 7 :=
  vec_set_pos (fun variable =>
    ra_quintic_resolvent_coefficient (ordinal_of_pos variable)).

Lemma encoded_quintic_resolvent_coefficients_mathcomp values :
  encoded_quintic_resolvent_coefficients values =
    encode_mathcomp_fixed_coefficients
      (quintic_resolvent_coefficients (decode_monic_quintic values)).
Proof.
  apply vec_pos_ext=> variable.
  rewrite /encoded_quintic_resolvent_coefficients
    /encode_mathcomp_fixed_coefficients
    /quintic_resolvent_coefficients !vec_pos_set vec_pos_map vec_pos_set.
  rewrite /quintic_resolvent_coefficient_code_expression
    eval_signed_zigzag_code_expression
    eval_quintic_resolvent_coefficient_expression.
  reflexivity.
Qed.

Lemma vec_list_quintic_resolvent_coefficients f :
  vec_list (quintic_resolvent_coefficients f) =
    QPS.quintic_scaled_resolvent f.
Proof.
  rewrite /quintic_resolvent_coefficients
    /QPS.quintic_scaled_resolvent vec_list_vec_set_pos.
  rewrite !enum_ordSl enum_ord0.
  cbn [pos_list List.map ordinal_of_pos pos2nat].
  reflexivity.
Qed.

Lemma leading_coefficient_length_seven (coefficients : seq int)
    (Hsize : size coefficients = 7%N)
    (Htop : nth 0 coefficients 6 != 0) :
  SRR.leading_coefficient coefficients = nth 0 coefficients 6.
Proof.
  rewrite /SRR.leading_coefficient.
  have Hpolynomial_size :
      size (SRR.coefficient_list_poly_int coefficients) = 7%N.
  { apply: (SRC.size_poly_from_top_coefficient (n := 6%N)).
    - by rewrite SRR.coefficient_list_poly_int_coef.
    - move=> index Hindex.
      rewrite SRR.coefficient_list_poly_int_coef nth_default // Hsize.
      exact: Hindex. }
  rewrite lead_coefE Hpolynomial_size.
  exact: SRR.coefficient_list_poly_int_coef.
Qed.

Definition quintic_resolvent_top_nonzero
    (f : QRF.monic_quintic) : Prop :=
  vec_pos (quintic_resolvent_coefficients f) (final_position 6) != 0.

(** This lemma isolates the only exact-degree seam in the generic bounded
    root search.  No coefficient normalization is used: once the last of
    the seven structurally compiled coefficients is known nonzero, the
    generic polynomial leading coefficient is definitionally that entry. *)
Lemma quintic_resolvent_leading_seam f
    (Htop : quintic_resolvent_top_nonzero f) :
  SRR.leading_coefficient
      (vec_list (quintic_resolvent_coefficients f)) =
    vec_pos (quintic_resolvent_coefficients f) (final_position 6).
Proof.
  apply: leading_coefficient_length_seven.
  - rewrite /quintic_resolvent_coefficients vec_list_vec_set_pos.
    reflexivity.
  - move: Htop.
    rewrite /quintic_resolvent_top_nonzero
      /quintic_resolvent_coefficients vec_pos_set.
    rewrite /quintic_resolvent_coefficients vec_list_vec_set_pos.
    cbn [pos_list List.map final_position].
    by move=> Htop'.
Qed.

Definition quintic_resolvent_last_index : 'I_7 := @Ordinal 7 6 isT.

Definition canonical_quintic_roots (f : QRF.monic_quintic) :
    5.-tuple (numfield (QCD.rational_monic_quintic f)) :=
  @QGA.quintic_root_tuple
    (QCD.rational_monic_quintic f)
    (QCD.size_rational_monic_quintic f).

(** Irreducibility discharges the top-nonzero seam structurally.  We
    compare coefficient six in the already proved polynomial identity;
    the scalar resolvent is monic of size seven, so its sixth coefficient
    is one, while the canonical homogeneous scale is nonzero. *)
Theorem quintic_resolvent_top_nonzero_irreducible f
    (Hfactor : QRF.has_bounded_proper_factor f = false) :
  quintic_resolvent_top_nonzero f.
Proof.
  have Hirreducible := QCD.rational_monic_quintic_irreducible Hfactor.
  have Hscale := QCD.canonical_quintic_resolvent_scale_nonzero Hirreducible.
  have Hpolynomial :=
    @QCD.quintic_scaled_resolvent_poly_correct
      (numfield (QCD.rational_monic_quintic f))
      (canonical_quintic_roots f) f
      (QCD.canonical_quintic_padded_vieta f).
  have Hscalar_coefficient :
      (QTV.quintic_scalar_resolvent (canonical_quintic_roots f))`_6 = 1.
  { have Hmonic := elimT monicP
      (QTV.quintic_scalar_resolvent_monic (canonical_quintic_roots f)).
    move: Hmonic.
    by rewrite lead_coefE QTV.size_quintic_scalar_resolvent. }
  have Hcoefficient := congr1
    (fun polynomial :
      {poly numfield (QCD.rational_monic_quintic f)} => polynomial`_6)
    Hpolynomial.
  rewrite coef_map SRR.coefficient_list_poly_int_coef
    (QPS.nth_quintic_scaled_resolvent f quintic_resolvent_last_index)
    coefZ Hscalar_coefficient mulr1 in Hcoefficient.
  have Hcoefficient_nonzero :
      ((QPS.quintic_scaled_resolvent_coefficient f
          quintic_resolvent_last_index)%:~R :
        numfield (QCD.rational_monic_quintic f)) != 0.
  { by rewrite Hcoefficient. }
  have Hinteger_nonzero :
      QPS.quintic_scaled_resolvent_coefficient f
        quintic_resolvent_last_index != 0.
  { apply/eqP=> Hzero.
    move: Hcoefficient_nonzero.
    by rewrite Hzero rmorph0 eqxx. }
  rewrite /quintic_resolvent_top_nonzero
    /quintic_resolvent_coefficients vec_pos_set.
  have Hindex : ordinal_of_pos (final_position 6) =
      quintic_resolvent_last_index by exact: val_inj.
  by rewrite Hindex.
Qed.

Lemma ra_quintic_resolvent_coefficient_component_correct variable values :
  ⟦vec_pos ra_quintic_resolvent_coefficients variable⟧ values
    (vec_pos (encoded_quintic_resolvent_coefficients values) variable).
Proof.
  rewrite /ra_quintic_resolvent_coefficients
    /encoded_quintic_resolvent_coefficients !vec_pos_set.
  unfold ra_quintic_resolvent_coefficient.
  exact: compile_nat_expression_correct.
Qed.

(** The relation exposes the entire seven-coefficient vector through the
    standard primitive-recursive vector pairing [inject]. *)
Definition quintic_resolvent_coefficient_vector_relation
    (values : Vector.t nat 5) (out : nat) : Prop :=
  out = inject (encoded_quintic_resolvent_coefficients values).

Definition ra_quintic_resolvent_coefficient_vector : recalg 5 :=
  ra_comp (ra_inject 7) ra_quintic_resolvent_coefficients.

Lemma ra_quintic_resolvent_coefficient_vector_correct values :
  ⟦ra_quintic_resolvent_coefficient_vector⟧ values
    (inject (encoded_quintic_resolvent_coefficients values)).
Proof.
  unfold ra_quintic_resolvent_coefficient_vector.
  exists (encoded_quintic_resolvent_coefficients values); split.
  - exact: ra_inject_val.
  - intro variable. rewrite vec_pos_set.
    exact: ra_quintic_resolvent_coefficient_component_correct.
Qed.

Theorem quintic_resolvent_coefficient_vector_relation_murec :
  MuRec_computable quintic_resolvent_coefficient_vector_relation.
Proof.
  unfold quintic_resolvent_coefficient_vector_relation.
  refine (@recalg_graph_murec 5
    (fun values => inject (encoded_quintic_resolvent_coefficients values))
    ra_quintic_resolvent_coefficient_vector _).
  exact: ra_quintic_resolvent_coefficient_vector_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* Composition with the generic fixed degree-six bounded-root program.   *)

Definition quintic_resolvent_rootb (values : Vector.t nat 5) : bool :=
  encoded_fixed_bounded_rootb 6
    (encoded_quintic_resolvent_coefficients values).

Theorem quintic_resolvent_rootb_mathcomp_true_iff f
    (Htop : quintic_resolvent_top_nonzero f) :
  quintic_resolvent_rootb (encode_monic_quintic f) = true <->
  SHR.bounded_homogeneous_rootb
    (QPS.quintic_scaled_resolvent f) = true.
Proof.
  rewrite /quintic_resolvent_rootb
    encoded_quintic_resolvent_coefficients_mathcomp
    decode_encode_monic_quintic.
  rewrite SHR.bounded_homogeneous_rootbE.
  rewrite -vec_list_quintic_resolvent_coefficients.
  exact: (@encoded_fixed_bounded_rootb_existing_true_iff 6
    (quintic_resolvent_coefficients f)
    (quintic_resolvent_leading_seam Htop)).
Qed.

Corollary quintic_resolvent_rootb_mathcomp f
    (Htop : quintic_resolvent_top_nonzero f) :
  quintic_resolvent_rootb (encode_monic_quintic f) =
  SHR.bounded_homogeneous_rootb (QPS.quintic_scaled_resolvent f).
Proof.
  apply Bool.eq_true_iff_eq.
  exact: quintic_resolvent_rootb_mathcomp_true_iff.
Qed.

Corollary quintic_resolvent_rootb_irreducible_mathcomp f
    (Hfactor : QRF.has_bounded_proper_factor f = false) :
  quintic_resolvent_rootb (encode_monic_quintic f) =
  SHR.bounded_homogeneous_rootb (QPS.quintic_scaled_resolvent f).
Proof.
  exact: quintic_resolvent_rootb_mathcomp
    (quintic_resolvent_top_nonzero_irreducible Hfactor).
Qed.

Definition ra_quintic_resolvent_root : recalg 5 :=
  ra_comp (ra_encoded_fixed_bounded_root 6)
    ra_quintic_resolvent_coefficients.

Lemma ra_quintic_resolvent_root_correct values :
  ⟦ra_quintic_resolvent_root⟧ values
    (bool_to_nat (quintic_resolvent_rootb values)).
Proof.
  unfold ra_quintic_resolvent_root, quintic_resolvent_rootb.
  exists (encoded_quintic_resolvent_coefficients values); split.
  - exact: ra_encoded_fixed_bounded_root_correct.
  - intro variable. rewrite vec_pos_set.
    exact: ra_quintic_resolvent_coefficient_component_correct.
Qed.

Definition quintic_resolvent_root_relation
    (values : Vector.t nat 5) (out : nat) : Prop :=
  out = bool_to_nat (quintic_resolvent_rootb values).

Theorem quintic_resolvent_root_relation_murec :
  MuRec_computable quintic_resolvent_root_relation.
Proof.
  unfold quintic_resolvent_root_relation.
  refine (@recalg_graph_murec 5
    (fun values => bool_to_nat (quintic_resolvent_rootb values))
    ra_quintic_resolvent_root _).
  exact: ra_quintic_resolvent_root_correct.
Qed.

(** A one-input endpoint consumes the standard pairing code of the five
    input coefficients. *)
Definition ra_quintic_resolvent_root_code : recalg 1 :=
  ra_comp ra_quintic_resolvent_root (ra_vec_project 5).

Lemma ra_quintic_resolvent_root_code_correct code :
  ⟦ra_quintic_resolvent_root_code⟧ (code ## vec_nil)
    (bool_to_nat (quintic_resolvent_rootb (project 5 code))).
Proof.
  unfold ra_quintic_resolvent_root_code.
  exists (project 5 code); split.
  - exact: ra_quintic_resolvent_root_correct.
  - intro variable. rewrite vec_pos_set.
    exact: ra_vec_project_val_at.
Qed.

Definition quintic_resolvent_root_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (quintic_resolvent_rootb (project 5 (vec_head code))).

Theorem quintic_resolvent_root_code_relation_murec :
  MuRec_computable quintic_resolvent_root_code_relation.
Proof.
  unfold quintic_resolvent_root_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (quintic_resolvent_rootb (project 5 (vec_head code))))
    ra_quintic_resolvent_root_code _).
  intro code_vector. vec split code_vector with code. vec nil code_vector.
  exact: ra_quintic_resolvent_root_code_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* The complete quintic Boolean: reducible, or resolvent has a root.      *)

Definition encoded_monic_quintic_radicalb
    (values : Vector.t nat 5) : bool :=
  QB.encoded_monic_quintic_has_proper_factorb values ||
    quintic_resolvent_rootb values.

Definition mathcomp_monic_quintic_radicalb
    (f : QRF.monic_quintic) : bool :=
  QRF.has_bounded_proper_factor f ||
    SHR.bounded_homogeneous_rootb (QPS.quintic_scaled_resolvent f).

Lemma bool_to_nat_orb left right :
  bool_to_nat (left || right) =
    ite_rel (bool_to_nat left) (bool_to_nat right) 1.
Proof. by case: left; case: right. Qed.

Definition ra_encoded_monic_quintic_radical : recalg 5 :=
  ra_comp ra_ite
    (QB.ra_encoded_monic_quintic_has_proper_factor ##
     ra_quintic_resolvent_root ##
     ra_cst_n 5 1 ## vec_nil).

Lemma ra_encoded_monic_quintic_radical_correct values :
  ⟦ra_encoded_monic_quintic_radical⟧ values
    (bool_to_nat (encoded_monic_quintic_radicalb values)).
Proof.
  rewrite /encoded_monic_quintic_radicalb bool_to_nat_orb.
  eapply ra_comp3_val.
  - exact: QB.ra_encoded_monic_quintic_has_proper_factor_correct.
  - exact: ra_quintic_resolvent_root_correct.
  - exact: ra_cst_n_val.
  - exact: ra_ite_val.
Qed.

Definition encoded_monic_quintic_radical_relation
    (values : Vector.t nat 5) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_quintic_radicalb values).

Theorem encoded_monic_quintic_radical_relation_murec :
  MuRec_computable encoded_monic_quintic_radical_relation.
Proof.
  unfold encoded_monic_quintic_radical_relation.
  refine (@recalg_graph_murec 5
    (fun values => bool_to_nat (encoded_monic_quintic_radicalb values))
    ra_encoded_monic_quintic_radical _).
  exact: ra_encoded_monic_quintic_radical_correct.
Qed.

(** On the irreducible branch, non-vanishing of the homogeneous top scale
    is the sole semantic hypothesis needed by the generic fixed-degree
    root search.  The reducible branch does not use this hypothesis. *)
Theorem encoded_monic_quintic_radicalb_mathcomp_with_top f
    (Hirreducible_top :
      QRF.has_bounded_proper_factor f = false ->
      quintic_resolvent_top_nonzero f) :
  encoded_monic_quintic_radicalb (encode_monic_quintic f) =
    mathcomp_monic_quintic_radicalb f.
Proof.
  rewrite /encoded_monic_quintic_radicalb
    /mathcomp_monic_quintic_radicalb.
  change
    (QB.encoded_monic_quintic_has_proper_factorb
       (QB.encode_monic_quintic_coefficients f) ||
       quintic_resolvent_rootb (encode_monic_quintic f) =
     QRF.has_bounded_proper_factor f ||
       SHR.bounded_homogeneous_rootb
         (QPS.quintic_scaled_resolvent f)).
  rewrite QB.encoded_monic_quintic_has_proper_factorb_mathcomp.
  case Hfactor: (QRF.has_bounded_proper_factor f)=> //=.
  exact: quintic_resolvent_rootb_mathcomp (Hirreducible_top Hfactor).
Qed.

Theorem encoded_monic_quintic_radicalb_mathcomp f :
  encoded_monic_quintic_radicalb (encode_monic_quintic f) =
    mathcomp_monic_quintic_radicalb f.
Proof.
  apply: encoded_monic_quintic_radicalb_mathcomp_with_top.
  exact: quintic_resolvent_top_nonzero_irreducible.
Qed.

Lemma mathcomp_monic_quintic_radicalb_QCD f :
  mathcomp_monic_quintic_radicalb f = QCD.quintic_radicalb f.
Proof. reflexivity. Qed.

Theorem encoded_monic_quintic_radicalb_QCD f :
  encoded_monic_quintic_radicalb (encode_monic_quintic f) =
    QCD.quintic_radicalb f.
Proof.
  rewrite encoded_monic_quintic_radicalb_mathcomp.
  exact: mathcomp_monic_quintic_radicalb_QCD.
Qed.

Lemma encoded_monic_quintic_radical_relation_mathcomp_with_top f
    (Hirreducible_top :
      QRF.has_bounded_proper_factor f = false ->
      quintic_resolvent_top_nonzero f) out :
  encoded_monic_quintic_radical_relation
      (encode_monic_quintic f) out <->
  out = bool_to_nat (mathcomp_monic_quintic_radicalb f).
Proof.
  rewrite /encoded_monic_quintic_radical_relation
    (encoded_monic_quintic_radicalb_mathcomp_with_top Hirreducible_top).
  reflexivity.
Qed.

Lemma encoded_monic_quintic_radical_relation_mathcomp f out :
  encoded_monic_quintic_radical_relation
      (encode_monic_quintic f) out <->
  out = bool_to_nat (mathcomp_monic_quintic_radicalb f).
Proof.
  rewrite /encoded_monic_quintic_radical_relation
    encoded_monic_quintic_radicalb_mathcomp.
  reflexivity.
Qed.

Lemma encoded_monic_quintic_radical_relation_QCD f out :
  encoded_monic_quintic_radical_relation
      (encode_monic_quintic f) out <->
  out = bool_to_nat (QCD.quintic_radicalb f).
Proof.
  rewrite encoded_monic_quintic_radical_relation_mathcomp
    mathcomp_monic_quintic_radicalb_QCD.
  reflexivity.
Qed.

Lemma ra_encoded_monic_quintic_radical_correct_QCD f :
  ⟦ra_encoded_monic_quintic_radical⟧ (encode_monic_quintic f)
    (bool_to_nat (QCD.quintic_radicalb f)).
Proof.
  rewrite -encoded_monic_quintic_radicalb_QCD.
  exact: ra_encoded_monic_quintic_radical_correct.
Qed.

Definition ra_encoded_monic_quintic_radical_code : recalg 1 :=
  ra_comp ra_encoded_monic_quintic_radical (ra_vec_project 5).

Lemma ra_encoded_monic_quintic_radical_code_correct code :
  ⟦ra_encoded_monic_quintic_radical_code⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_monic_quintic_radicalb (project 5 code))).
Proof.
  unfold ra_encoded_monic_quintic_radical_code.
  exists (project 5 code); split.
  - exact: ra_encoded_monic_quintic_radical_correct.
  - intro variable. rewrite vec_pos_set.
    exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_quintic_radical_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_quintic_radicalb (project 5 (vec_head code))).

Theorem encoded_monic_quintic_radical_code_relation_murec :
  MuRec_computable encoded_monic_quintic_radical_code_relation.
Proof.
  unfold encoded_monic_quintic_radical_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (encoded_monic_quintic_radicalb (project 5 (vec_head code))))
    ra_encoded_monic_quintic_radical_code _).
  intro code_vector. vec split code_vector with code. vec nil code_vector.
  exact: ra_encoded_monic_quintic_radical_code_correct.
Qed.

Lemma encoded_monic_quintic_radical_code_relation_mathcomp_with_top f
    (Hirreducible_top :
      QRF.has_bounded_proper_factor f = false ->
      quintic_resolvent_top_nonzero f) out :
  encoded_monic_quintic_radical_code_relation
      (inject (encode_monic_quintic f) ## vec_nil) out <->
  out = bool_to_nat (mathcomp_monic_quintic_radicalb f).
Proof.
  rewrite /encoded_monic_quintic_radical_code_relation.
  cbn [vec_head].
  rewrite project_inject
    (encoded_monic_quintic_radicalb_mathcomp_with_top Hirreducible_top).
  reflexivity.
Qed.

Lemma encoded_monic_quintic_radical_code_relation_mathcomp f out :
  encoded_monic_quintic_radical_code_relation
      (inject (encode_monic_quintic f) ## vec_nil) out <->
  out = bool_to_nat (mathcomp_monic_quintic_radicalb f).
Proof.
  rewrite /encoded_monic_quintic_radical_code_relation.
  cbn [vec_head].
  rewrite project_inject encoded_monic_quintic_radicalb_mathcomp.
  reflexivity.
Qed.

Lemma encoded_monic_quintic_radical_code_relation_QCD f out :
  encoded_monic_quintic_radical_code_relation
      (inject (encode_monic_quintic f) ## vec_nil) out <->
  out = bool_to_nat (QCD.quintic_radicalb f).
Proof.
  rewrite encoded_monic_quintic_radical_code_relation_mathcomp
    mathcomp_monic_quintic_radicalb_QCD.
  reflexivity.
Qed.

Lemma ra_encoded_monic_quintic_radical_code_correct_QCD f :
  ⟦ra_encoded_monic_quintic_radical_code⟧
    (inject (encode_monic_quintic f) ## vec_nil)
    (bool_to_nat (QCD.quintic_radicalb f)).
Proof.
  move: (ra_encoded_monic_quintic_radical_code_correct
    (inject (encode_monic_quintic f))).
  by rewrite project_inject encoded_monic_quintic_radicalb_QCD.
Qed.

End PolynomialFormulasSexticMuRecQuinticResolvent.

Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.eval_quintic_resolvent_coefficient_expression.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.quintic_resolvent_coefficient_vector_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.quintic_resolvent_root_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.quintic_resolvent_root_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.quintic_resolvent_top_nonzero_irreducible.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.encoded_monic_quintic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.encoded_monic_quintic_radical_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.ra_encoded_monic_quintic_radical_correct_QCD.
Print Assumptions
  PolynomialFormulasSexticMuRecQuinticResolvent.ra_encoded_monic_quintic_radical_code_correct_QCD.
