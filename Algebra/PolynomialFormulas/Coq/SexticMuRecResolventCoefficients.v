(* ===================================================================== *)
(*  Mu-recursive construction of the computed sextic resolvent lists.    *)
(*                                                                       *)
(*  This file is deliberately separate from the checkpointed generic    *)
(*  bounded-root compiler.  Besides the coefficient compiler developed  *)
(*  below, it records the exact list/vector and leading-coefficient       *)
(*  interfaces needed to feed the generated vectors to that compiler.    *)
(* ===================================================================== *)

From Stdlib Require Import Lia List Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.

From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.

From PolynomialFormulas Require Import SexticMuRecComputability
  SexticRecursiveCore SexticSparseResolvents SexticResolventSymmetry
  SexticComputedResolvents SexticRationalRootSearch
  SexticComputedResolventBridge SexticDescriptorGaloisCriterion
  SexticCanonicalVieta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecResolventCoefficients.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SSR := PolynomialFormulasSexticSparseResolvents.
Module SRS := PolynomialFormulasSexticResolventSymmetry.
Module SCR := PolynomialFormulasSexticComputedResolvents.
Module SRR := PolynomialFormulasSexticRationalRootSearch.
Module SCRB := PolynomialFormulasSexticComputedResolventBridge.
Module SCV := PolynomialFormulasSexticCanonicalVieta.
Module SDGC := PolynomialFormulasSexticDescriptorGaloisCriterion.

Import SRC.
Import SSR.
Import SRS.
Import SCR.

(* --------------------------------------------------------------------- *)
(* Fixed lists as the vectors consumed by the generic root compiler.      *)

Definition fixed_vector_of_list {A : Type} {count : nat}
    (values : list A) (Hsize : List.length values = count) :
    Vector.t A count :=
  eq_rect (List.length values) (Vector.t A) (list_vec values) count Hsize.

Lemma vec_list_fixed_vector_of_list {A : Type} {count : nat}
    (values : list A) (Hsize : List.length values = count) :
  vec_list (@fixed_vector_of_list A count values Hsize) = values.
Proof.
  destruct Hsize.
  exact: list_vec_iso.
Qed.

Definition pair_scaled_resolvent_vector
    (f : monic_sextic) (x : parameter) : Vector.t int 16 :=
  @fixed_vector_of_list int 16 (pair_scaled_resolvent f x)
    (size_pair_scaled_resolvent f x).

Definition triple_scaled_resolvent_vector
    (f : monic_sextic) (x : parameter) : Vector.t int 11 :=
  @fixed_vector_of_list int 11 (triple_scaled_resolvent f x)
    (size_triple_scaled_resolvent f x).

Lemma vec_list_pair_scaled_resolvent_vector f x :
  vec_list (pair_scaled_resolvent_vector f x) =
  pair_scaled_resolvent f x.
Proof. exact: vec_list_fixed_vector_of_list. Qed.

Lemma vec_list_triple_scaled_resolvent_vector f x :
  vec_list (triple_scaled_resolvent_vector f x) =
  triple_scaled_resolvent f x.
Proof. exact: vec_list_fixed_vector_of_list. Qed.

Lemma vec_pos_final_nth {A : Type} degree
    (values : Vector.t A degree.+1) (default : A) :
  vec_pos values (final_position degree) =
  List.nth degree (vec_list values) default.
Proof.
  elim: degree values=> [|degree IH] values.
  - vec split values with value. vec nil values. reflexivity.
  - vec split values with value. cbn [final_position vec_list vec_pos].
    exact: IH.
Qed.

Lemma mathcomp_nth_List_nth {A : Type} (default : A)
    (values : seq A) index :
  nth default values index = List.nth index values default.
Proof.
  elim: values index=> [|value values IH] [|index] //=.
Qed.

Lemma leading_coefficient_fixed_list (values : seq int) degree
    (Hsize : size values = degree.+1)
    (Hlast : nth 0 values degree != 0) :
  SRR.leading_coefficient values = nth 0 values degree.
Proof.
  have Hpoly_size :
      size (SRR.coefficient_list_poly_int values) = degree.+1.
  { apply: SRC.size_poly_from_top_coefficient.
    - by rewrite SRR.coefficient_list_poly_int_coef.
    - move=> index Hdegree_index.
      rewrite SRR.coefficient_list_poly_int_coef nth_default // Hsize.
      exact: Hdegree_index. }
  rewrite /SRR.leading_coefficient lead_coefE Hpoly_size.
  by rewrite SRR.coefficient_list_poly_int_coef.
Qed.

(* --------------------------------------------------------------------- *)
(* The common leading coefficient of both computed resolvents is 720.    *)

Lemma pair_semantic_resolvent_monic (roots : 6.-tuple algC) x :
  SRS.coefficient_list_poly roots (pair_sparse_resolvent x) \is monic.
Proof.
  rewrite SRS.coefficient_list_poly_pair_resolvent.
  exact: monic_prod_XsubC.
Qed.

Lemma triple_semantic_resolvent_monic (roots : 6.-tuple algC) x :
  SRS.coefficient_list_poly roots (triple_sparse_resolvent x) \is monic.
Proof.
  rewrite SRS.coefficient_list_poly_triple_resolvent.
  exact: monic_prod_XsubC.
Qed.

Lemma size_pair_semantic_resolvent (roots : 6.-tuple algC) x :
  size (SRS.coefficient_list_poly roots (pair_sparse_resolvent x)) = 16%N.
Proof.
  rewrite SRS.coefficient_list_poly_pair_resolvent size_prod_XsubC.
  by rewrite [index_enum _]unlock -enumT size_enum_ord.
Qed.

Lemma size_triple_semantic_resolvent (roots : 6.-tuple algC) x :
  size (SRS.coefficient_list_poly roots (triple_sparse_resolvent x)) = 11%N.
Proof.
  rewrite SRS.coefficient_list_poly_triple_resolvent size_prod_XsubC.
  by rewrite [index_enum _]unlock -enumT size_enum_ord.
Qed.

Lemma pair_scaled_resolvent_last f x :
  nth 0 (pair_scaled_resolvent f x) 15 = 720.
Proof.
  pose roots := @SDGC.sextic_complex_root_tuple
    (SCV.rational_monic_sextic f) (SCV.size_rational_monic_sextic f).
  pose semantic := SRS.coefficient_list_poly roots
    (pair_sparse_resolvent x).
  have Hsemantic_monic : semantic \is monic.
  { exact: pair_semantic_resolvent_monic. }
  have Hsemantic_size : size semantic = 16%N.
  { exact: size_pair_semantic_resolvent. }
  have Hsemantic_top : semantic`_15 = 1.
  { move/eqP: Hsemantic_monic.
    by rewrite lead_coefE Hsemantic_size. }
  have Hpoly := @SCRB.pair_scaled_resolvent_poly_correct
    algC roots f x (SCV.canonical_monic_sextic_vieta f).
  have Hcoefficient := congr1 (fun p : {poly algC} => p`_15) Hpoly.
  apply: (@intr_inj algC).
  move: Hcoefficient.
  rewrite coef_map SRR.coefficient_list_poly_int_coef coefZ
    Hsemantic_top mulr1.
  by rewrite rmorph_nat.
Qed.

Lemma triple_scaled_resolvent_last f x :
  nth 0 (triple_scaled_resolvent f x) 10 = 720.
Proof.
  pose roots := @SDGC.sextic_complex_root_tuple
    (SCV.rational_monic_sextic f) (SCV.size_rational_monic_sextic f).
  pose semantic := SRS.coefficient_list_poly roots
    (triple_sparse_resolvent x).
  have Hsemantic_monic : semantic \is monic.
  { exact: triple_semantic_resolvent_monic. }
  have Hsemantic_size : size semantic = 11%N.
  { exact: size_triple_semantic_resolvent. }
  have Hsemantic_top : semantic`_10 = 1.
  { move/eqP: Hsemantic_monic.
    by rewrite lead_coefE Hsemantic_size. }
  have Hpoly := @SCRB.triple_scaled_resolvent_poly_correct
    algC roots f x (SCV.canonical_monic_sextic_vieta f).
  have Hcoefficient := congr1 (fun p : {poly algC} => p`_10) Hpoly.
  apply: (@intr_inj algC).
  move: Hcoefficient.
  rewrite coef_map SRR.coefficient_list_poly_int_coef coefZ
    Hsemantic_top mulr1.
  by rewrite rmorph_nat.
Qed.

Lemma pair_scaled_resolvent_leading f x :
  SRR.leading_coefficient (pair_scaled_resolvent f x) = 720.
Proof.
  rewrite (leading_coefficient_fixed_list
    (size_pair_scaled_resolvent f x)).
  - exact: pair_scaled_resolvent_last.
  - by rewrite pair_scaled_resolvent_last.
Qed.

Lemma triple_scaled_resolvent_leading f x :
  SRR.leading_coefficient (triple_scaled_resolvent f x) = 720.
Proof.
  rewrite (leading_coefficient_fixed_list
    (size_triple_scaled_resolvent f x)).
  - exact: triple_scaled_resolvent_last.
  - by rewrite triple_scaled_resolvent_last.
Qed.

Lemma pair_scaled_resolvent_vector_final f x :
  vec_pos (pair_scaled_resolvent_vector f x) (final_position 15) = 720.
Proof.
  rewrite (@vec_pos_final_nth int 15 (pair_scaled_resolvent_vector f x) 0)
    vec_list_pair_scaled_resolvent_vector.
  rewrite -mathcomp_nth_List_nth.
  exact: pair_scaled_resolvent_last.
Qed.

Lemma triple_scaled_resolvent_vector_final f x :
  vec_pos (triple_scaled_resolvent_vector f x) (final_position 10) = 720.
Proof.
  rewrite (@vec_pos_final_nth int 10 (triple_scaled_resolvent_vector f x) 0)
    vec_list_triple_scaled_resolvent_vector.
  rewrite -mathcomp_nth_List_nth.
  exact: triple_scaled_resolvent_last.
Qed.

Theorem pair_scaled_resolvent_vector_leading_identity f x :
  SRR.leading_coefficient
      (vec_list (pair_scaled_resolvent_vector f x)) =
    vec_pos (pair_scaled_resolvent_vector f x) (final_position 15).
Proof.
  rewrite vec_list_pair_scaled_resolvent_vector
    pair_scaled_resolvent_leading pair_scaled_resolvent_vector_final.
  reflexivity.
Qed.

Theorem triple_scaled_resolvent_vector_leading_identity f x :
  SRR.leading_coefficient
      (vec_list (triple_scaled_resolvent_vector f x)) =
    vec_pos (triple_scaled_resolvent_vector f x) (final_position 10).
Proof.
  rewrite vec_list_triple_scaled_resolvent_vector
    triple_scaled_resolvent_leading triple_scaled_resolvent_vector_final.
  reflexivity.
Qed.

Corollary encoded_pair_scaled_resolvent_rootb_true_iff f x :
  encoded_pair_resolvent_bounded_rootb
      (encode_mathcomp_fixed_coefficients
        (pair_scaled_resolvent_vector f x)) = true <->
  SRR.pair_scaled_rational_rootb f x = true.
Proof.
  rewrite /encoded_pair_resolvent_bounded_rootb
    /SRR.pair_scaled_rational_rootb
    -vec_list_pair_scaled_resolvent_vector.
  exact: (@encoded_fixed_bounded_rootb_existing_true_iff
    15 (pair_scaled_resolvent_vector f x)
    (pair_scaled_resolvent_vector_leading_identity f x)).
Qed.

Corollary encoded_triple_scaled_resolvent_rootb_true_iff f x :
  encoded_triple_resolvent_bounded_rootb
      (encode_mathcomp_fixed_coefficients
        (triple_scaled_resolvent_vector f x)) = true <->
  SRR.triple_scaled_rational_rootb f x = true.
Proof.
  rewrite /encoded_triple_resolvent_bounded_rootb
    /SRR.triple_scaled_rational_rootb
    -vec_list_triple_scaled_resolvent_vector.
  exact: (@encoded_fixed_bounded_rootb_existing_true_iff
    10 (triple_scaled_resolvent_vector f x)
    (triple_scaled_resolvent_vector_leading_identity f x)).
Qed.

Print Assumptions pair_scaled_resolvent_last.
Print Assumptions triple_scaled_resolvent_last.
Print Assumptions pair_scaled_resolvent_vector_leading_identity.
Print Assumptions triple_scaled_resolvent_vector_leading_identity.
Print Assumptions encoded_pair_scaled_resolvent_rootb_true_iff.
Print Assumptions encoded_triple_scaled_resolvent_rootb_true_iff.

End PolynomialFormulasSexticMuRecResolventCoefficients.
