From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticGaloisAction QuinticRecursiveFactor
  QuinticCanonicalDecision
  LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance LazardQuinticRootCentering
  LazardQuinticGeneralDepression
  LazardQuinticRootBranchSelectionReconstruction
  LazardQuinticInvariantDescentF20
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The coefficient bridge from an arbitrary ordered five-root tuple to
    the general and depressed quintics used by the formula modules.

    The general quintic is defined by the five elementary symmetric
    functions.  Its Tschirnhaus depression is proved, coefficient by
    coefficient, to be exactly the quintic defined by subtracting the
    average of the five roots.  Thus the coefficient-matching premise of
    the general reconstruction theorem is a theorem, rather than an
    externally supplied Vieta certificate. *)
Module PolynomialFormulasLazardQuinticRootCoefficientBridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module GD := PolynomialFormulasLazardQuinticGeneralDepression.
Module BSR :=
  PolynomialFormulasLazardQuinticRootBranchSelectionReconstruction.
Module GF := PolynomialFormulasLazardQuinticGeneralFormulaReconstruction.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.

Local Open Scope ring_scope.

Section RootCoefficientBridge.

Variable F : fieldType.

Add Ring lazard_root_coefficient_bridge_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_coefficient_bridge_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Raw translation identities.  These do not yet use that the translation
    amount is one fifth of the first elementary symmetric function. *)
Lemma lazard_centered_esymm2_raw roots :
  RP.lazard_root_esymm2 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm2 roots -
      4%:R * RC.lazard_root_center roots *
        RP.lazard_root_esymm1 roots +
      10%:R * RC.lazard_root_center roots ^+ 2.
Proof.
rewrite /RP.lazard_root_esymm1 /RP.lazard_root_esymm2
  !RC.tnth_lazard_centered_roots.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm3_raw roots :
  RP.lazard_root_esymm3 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm3 roots -
      3%:R * RC.lazard_root_center roots *
        RP.lazard_root_esymm2 roots +
      6%:R * RC.lazard_root_center roots ^+ 2 *
        RP.lazard_root_esymm1 roots -
      10%:R * RC.lazard_root_center roots ^+ 3.
Proof.
rewrite /RP.lazard_root_esymm1 /RP.lazard_root_esymm2
  /RP.lazard_root_esymm3 !RC.tnth_lazard_centered_roots.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm4_raw roots :
  RP.lazard_root_esymm4 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm4 roots -
      2%:R * RC.lazard_root_center roots *
        RP.lazard_root_esymm3 roots +
      3%:R * RC.lazard_root_center roots ^+ 2 *
        RP.lazard_root_esymm2 roots -
      4%:R * RC.lazard_root_center roots ^+ 3 *
        RP.lazard_root_esymm1 roots +
      5%:R * RC.lazard_root_center roots ^+ 4.
Proof.
rewrite /RP.lazard_root_esymm1 /RP.lazard_root_esymm2
  /RP.lazard_root_esymm3 /RP.lazard_root_esymm4
  !RC.tnth_lazard_centered_roots.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm5_raw roots :
  RP.lazard_root_esymm5 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm5 roots -
      RC.lazard_root_center roots * RP.lazard_root_esymm4 roots +
      RC.lazard_root_center roots ^+ 2 * RP.lazard_root_esymm3 roots -
      RC.lazard_root_center roots ^+ 3 * RP.lazard_root_esymm2 roots +
      RC.lazard_root_center roots ^+ 4 * RP.lazard_root_esymm1 roots -
      RC.lazard_root_center roots ^+ 5.
Proof.
rewrite /RP.lazard_root_esymm1 /RP.lazard_root_esymm2
  /RP.lazard_root_esymm3 /RP.lazard_root_esymm4
  /RP.lazard_root_esymm5 !RC.tnth_lazard_centered_roots.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_root_center_times_five roots
    (five_neq0 : (5%:R : F) != 0) :
  RC.lazard_root_center roots * 5%:R = RP.lazard_root_esymm1 roots.
Proof.
rewrite /RC.lazard_root_center.
exact: divfK five_neq0.
Qed.

(** The four elementary symmetric functions of the centered tuple. *)
Lemma lazard_centered_esymm2 roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_esymm2 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm2 roots -
      10%:R * RC.lazard_root_center roots ^+ 2.
Proof.
rewrite lazard_centered_esymm2_raw
  -(lazard_root_center_times_five roots five_neq0).
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm3 roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_esymm3 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm3 roots -
      3%:R * RC.lazard_root_center roots *
        RP.lazard_root_esymm2 roots +
      20%:R * RC.lazard_root_center roots ^+ 3.
Proof.
rewrite lazard_centered_esymm3_raw
  -(lazard_root_center_times_five roots five_neq0).
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm4 roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_esymm4 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm4 roots -
      2%:R * RC.lazard_root_center roots *
        RP.lazard_root_esymm3 roots +
      3%:R * RC.lazard_root_center roots ^+ 2 *
        RP.lazard_root_esymm2 roots -
      15%:R * RC.lazard_root_center roots ^+ 4.
Proof.
rewrite lazard_centered_esymm4_raw
  -(lazard_root_center_times_five roots five_neq0).
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_centered_esymm5 roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_esymm5 (RC.lazard_centered_roots roots) =
    RP.lazard_root_esymm5 roots -
      RC.lazard_root_center roots * RP.lazard_root_esymm4 roots +
      RC.lazard_root_center roots ^+ 2 * RP.lazard_root_esymm3 roots -
      RC.lazard_root_center roots ^+ 3 * RP.lazard_root_esymm2 roots +
      4%:R * RC.lazard_root_center roots ^+ 5.
Proof.
rewrite lazard_centered_esymm5_raw
  -(lazard_root_center_times_five roots five_neq0).
finish_lazard_root_coefficient_bridge_ring.
Qed.

(** The unique monic quintic whose ordered roots are [roots]. *)
Definition lazard_general_of_roots (roots : 5.-tuple F) :
    GD.LazardGeneralQuinticCoefficients F :=
  @GD.Build_LazardGeneralQuinticCoefficients F
    1 (- RP.lazard_root_esymm1 roots)
    (RP.lazard_root_esymm2 roots)
    (- RP.lazard_root_esymm3 roots)
    (RP.lazard_root_esymm4 roots)
    (- RP.lazard_root_esymm5 roots).

Lemma lazard_general_of_roots_leading roots :
  GD.lazard_general_a (lazard_general_of_roots roots) = 1.
Proof. reflexivity. Qed.

Lemma lazard_general_of_roots_leading_neq0 roots :
  GD.lazard_general_a (lazard_general_of_roots roots) != 0.
Proof. by rewrite lazard_general_of_roots_leading oner_eq0. Qed.

Lemma lazard_general_of_roots_depression_shift roots :
  GD.lazard_depression_shift (lazard_general_of_roots roots) =
    - RC.lazard_root_center roots.
Proof.
rewrite /GD.lazard_depression_shift /lazard_general_of_roots
  /RC.lazard_root_center /=.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_depress_general_of_roots_p roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_p
      (GD.lazard_depress_general (lazard_general_of_roots roots)) =
    RP.lazard_root_esymm2 (RC.lazard_centered_roots roots).
Proof.
rewrite /GD.lazard_depress_general /=
  lazard_general_of_roots_depression_shift
  lazard_centered_esymm2 //.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_depress_general_of_roots_q roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_q
      (GD.lazard_depress_general (lazard_general_of_roots roots)) =
    - RP.lazard_root_esymm3 (RC.lazard_centered_roots roots).
Proof.
rewrite /GD.lazard_depress_general /=
  lazard_general_of_roots_depression_shift
  lazard_centered_esymm3 //.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_depress_general_of_roots_r roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_r
      (GD.lazard_depress_general (lazard_general_of_roots roots)) =
    RP.lazard_root_esymm4 (RC.lazard_centered_roots roots).
Proof.
rewrite /GD.lazard_depress_general /=
  lazard_general_of_roots_depression_shift
  lazard_centered_esymm4 //.
finish_lazard_root_coefficient_bridge_ring.
Qed.

Lemma lazard_depress_general_of_roots_s roots
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_s
      (GD.lazard_depress_general (lazard_general_of_roots roots)) =
    - RP.lazard_root_esymm5 (RC.lazard_centered_roots roots).
Proof.
rewrite /GD.lazard_depress_general /=
  lazard_general_of_roots_depression_shift
  lazard_centered_esymm5 //.
finish_lazard_root_coefficient_bridge_ring.
Qed.

(** The formerly supplied coefficient certificate. *)
Theorem lazard_depress_general_of_roots roots
    (five_neq0 : (5%:R : F) != 0) :
  GD.lazard_depress_general (lazard_general_of_roots roots) =
    RP.lazard_depressed_of_roots (RC.lazard_centered_roots roots).
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- exact: lazard_depress_general_of_roots_p.
- exact: lazard_depress_general_of_roots_q.
- exact: lazard_depress_general_of_roots_r.
- exact: lazard_depress_general_of_roots_s.
Qed.

(** Exact Vieta factorization of the root-defined general quintic. *)
Theorem lazard_general_of_roots_eval_factorization roots (x : F) :
  GD.lazard_general_quintic_eval (lazard_general_of_roots roots) x =
    (x - tnth roots o0) * (x - tnth roots o1) *
    (x - tnth roots o2) * (x - tnth roots o3) *
    (x - tnth roots o4).
Proof.
rewrite /GD.lazard_general_quintic_eval /lazard_general_of_roots /=
  /RP.lazard_root_esymm1 /RP.lazard_root_esymm2
  /RP.lazard_root_esymm3 /RP.lazard_root_esymm4
  /RP.lazard_root_esymm5.
finish_lazard_root_coefficient_bridge_ring.
Qed.

(** The finite-product form used by the canonical splitting-field
    factorization.  Keeping the tuple bookkeeping separate makes the
    canonical bridge below depend only on the exact polynomial
    factorization, not on a second coefficient comparison. *)
Lemma lazard_five_tuple_linear_productE roots (x : F) :
  \prod_(r <- roots) (x - r) =
    (x - tnth roots o0) * (x - tnth roots o1) *
    (x - tnth roots o2) * (x - tnth roots o3) *
    (x - tnth roots o4).
Proof.
rewrite -(map_tnth_enum roots) big_map big_enum.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 4) = o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) = o4
  by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 mulr1 !mulrA.
Qed.

Lemma lazard_horner_prod_XsubC_five roots (x : F) :
  (\prod_(r <- roots) ('X - r%:P : {poly F})).[x] =
    (x - tnth roots o0) * (x - tnth roots o1) *
    (x - tnth roots o2) * (x - tnth roots o3) *
    (x - tnth roots o4).
Proof.
rewrite horner_prod.
transitivity (\prod_(r <- roots) (x - r)).
- apply: eq_bigr=> r _.
  exact: hornerXsubC.
- exact: lazard_five_tuple_linear_productE.
Qed.

(** Any exact monic linear-factor certificate identifies the evaluator of
    [lazard_general_of_roots] with the certified polynomial. *)
Theorem lazard_general_of_roots_eval_of_factorization roots
    (p : {poly F})
    (hfactor : p =
      \prod_(r <- roots) ('X - r%:P : {poly F})) (x : F) :
  GD.lazard_general_quintic_eval (lazard_general_of_roots roots) x = p.[x].
Proof.
rewrite lazard_general_of_roots_eval_factorization hfactor
  lazard_horner_prod_XsubC_five.
reflexivity.
Qed.

Lemma lazard_centered_root_translate_back roots (k : 'I_5) :
  tnth (RC.lazard_centered_roots roots) k -
      GD.lazard_depression_shift (lazard_general_of_roots roots) =
    tnth roots k.
Proof.
rewrite RC.tnth_lazard_centered_roots
  lazard_general_of_roots_depression_shift.
finish_lazard_root_coefficient_bridge_ring.
Qed.

(** General-quintic reconstruction specialized to the coefficients of its
    actual roots.  In particular, no coefficient-matching certificate is
    exposed by this theorem. *)
Theorem lazard_exists_root_derived_general_formula_complete
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : FN.lazard_invariant_E
      (RP.lazard_depressed_of_roots (RC.lazard_centered_roots roots))
      (RP.lazard_root_invariants (RC.lazard_centered_roots roots)) != 0) :
  exists first second : Q.lazard_sign_branch,
    (forall x : F,
      GD.lazard_general_quintic_eval (lazard_general_of_roots roots) x =
      (x - GF.lazard_general_formula_output_two_branches
        (lazard_general_of_roots roots) omega
        (RC.lazard_centered_roots roots) first second o0) *
      (x - GF.lazard_general_formula_output_two_branches
        (lazard_general_of_roots roots) omega
        (RC.lazard_centered_roots roots) first second o1) *
      (x - GF.lazard_general_formula_output_two_branches
        (lazard_general_of_roots roots) omega
        (RC.lazard_centered_roots roots) first second o2) *
      (x - GF.lazard_general_formula_output_two_branches
        (lazard_general_of_roots roots) omega
        (RC.lazard_centered_roots roots) first second o3) *
      (x - GF.lazard_general_formula_output_two_branches
        (lazard_general_of_roots roots) omega
        (RC.lazard_centered_roots roots) first second o4)) /\
    (forall k : 'I_5,
      GD.lazard_general_quintic_eval (lazard_general_of_roots roots)
        (GF.lazard_general_formula_output_two_branches
          (lazard_general_of_roots roots) omega
          (RC.lazard_centered_roots roots) first second k) = 0) /\
    (forall x : F,
      GD.lazard_general_quintic_eval (lazard_general_of_roots roots) x = 0 ->
      exists k : 'I_5,
        x = GF.lazard_general_formula_output_two_branches
          (lazard_general_of_roots roots) omega
          (RC.lazard_centered_roots roots) first second k).
Proof.
have hcentered_injective :
    injective (tnth (RC.lazard_centered_roots roots)).
  exact: RC.lazard_centered_roots_injective hroots.
have hcentered_sum :
    RP.lazard_root_esymm1 (RC.lazard_centered_roots roots) = 0.
  exact: RC.lazard_centered_roots_sum_zero five_neq0.
have hcentered_epsilon :
    RP.lazard_root_epsilon omega (RC.lazard_centered_roots roots) != 0.
  by rewrite RC.lazard_root_epsilon_centered.
have hcoeff := lazard_depress_general_of_roots roots five_neq0.
have h := @BSR.lazard_exists_general_formula_complete F
  (lazard_general_of_roots roots)
  (lazard_general_of_roots_leading_neq0 roots)
  omega (RC.lazard_centered_roots roots)
  two_neq0 five_neq0 omega_primitive hcentered_injective
  hcentered_sum hcentered_epsilon E_neq0 hcoeff.
move: h.
by rewrite lazard_general_of_roots_leading mul1r.
Qed.

End RootCoefficientBridge.

(** The canonical tuple and every selected Lazard ordering define exactly
    the original rational monic quintic after mapping it into its canonical
    splitting field.  The selected statement is the bridge used by the
    end-to-end solver: its input ordering may differ from the canonical
    enumeration, but only by a permutation. *)
Section CanonicalCoefficientBridge.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

Theorem lazard_general_of_canonical_roots_eval (x : L) :
  GD.lazard_general_quintic_eval (lazard_general_of_roots roots) x =
    (map_poly ratrL p).[x].
Proof.
apply: lazard_general_of_roots_eval_of_factorization.
exact: CD.canonical_quintic_numfield_factorization.
Qed.

Lemma lazard_selected_canonical_roots_factorization (i : 'I_6) :
  map_poly ratrL p =
    \prod_(r <- ID.lazard_selected_roots i)
      ('X - r%:P : {poly L}).
Proof.
rewrite /ID.lazard_selected_roots
  CE.lazard_prod_XsubC_permute_quintic.
exact: CD.canonical_quintic_numfield_factorization.
Qed.

Theorem lazard_general_of_selected_canonical_roots_eval
    (i : 'I_6) (x : L) :
  GD.lazard_general_quintic_eval
      (lazard_general_of_roots (ID.lazard_selected_roots i)) x =
    (map_poly ratrL p).[x].
Proof.
apply: lazard_general_of_roots_eval_of_factorization.
exact: lazard_selected_canonical_roots_factorization.
Qed.

End CanonicalCoefficientBridge.

End PolynomialFormulasLazardQuinticRootCoefficientBridge.
