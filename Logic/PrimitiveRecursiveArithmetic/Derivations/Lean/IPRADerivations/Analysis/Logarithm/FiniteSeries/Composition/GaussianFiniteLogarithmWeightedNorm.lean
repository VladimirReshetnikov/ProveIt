import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDilation
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmPolynomial
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianIntegerFractionPowers
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormEntries

/-!
# The auxiliary-radius coefficient majorant of the original finite logarithm

The logarithmic coefficients and positive-axis powers retain their actual
native signed representations. Their L1 bounds are derived, then summed
through the original descending stored coefficients. This is a finite
weighted-norm supplier for C4, not an analytic logarithm identity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmWeightedNorm

open_ipra
open GaussianRationalHorner (qmul represents)
open GaussianFiniteLogarithmPolynomial (coefficient signNumerator polynomial)
open GaussianRationalReciprocal (power)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator)
open GaussianRationalL1 (qL1)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalArgmin (rationalLE)
open GaussianCoefficientL1 (prefixNorm coefficientNorm)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem radius_norm1 (A : PTm n) : Γ ⊢[PRAAx] GaussianL1.norm1 (radiusNumerator A) ≐ A := by
  have r : Γ ⊢[PRAAx] Foundations.GapDecision.zabs (ComplexLogarithmRemainder.re (radiusNumerator A)) ≐ A :=
    (Foundations.GapDecision.zabs_congr (v := ZT.ofNat A) (by
      simp only [radiusNumerator,ComplexLogarithmRemainder.eval_re_code])).eqTrans (GaussianL1.abs_ofNat A)
  have i : Γ ⊢[PRAAx] Foundations.GapDecision.zabs (ComplexLogarithmRemainder.im (radiusNumerator A)) ≐ zero :=
    (Foundations.GapDecision.zabs_congr (v := ZT.ofNat zero) (by
      simp only [radiusNumerator,ComplexLogarithmRemainder.eval_im_code])).eqTrans (GaussianL1.abs_ofNat zero)
  exact (congrAdd r i).eqTrans (add_zero A)

theorem sign_norm1 (k : PTm n) : Γ ⊢[PRAAx] GaussianL1.norm1 (signNumerator k) ≐ one := by
  have all : Γ ⊢[PRAAx] .all (GaussianL1.norm1 (signNumerator (var 0)) ≐ one) := by
    ipra_qfind [GaussianL1.subst_norm1, GaussianFiniteLogarithmPolynomial.subst_signNumerator]
    · exact (GaussianL1.norm1_equal GaussianIntegerFractionPowers.parity_scalar_zero).eqTrans GaussianL1.norm1_one
    · exact (GaussianL1.norm1_equal (GaussianIntegerFractionPowers.parity_scalar_succ (var 0))).eqTrans
        ((GaussianL1.norm1_negative _).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,GaussianL1.subst_norm1,GaussianFiniteLogarithmPolynomial.subst_signNumerator,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero] using all.allE k

theorem l1_from_representation (q a A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a D) (hA : Γ ⊢[PRAAx] GaussianL1.norm1 a ≐ A) :
    Γ ⊢[PRAAx] qL1 q ≐ fraction A D := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalL1.qL1_guard q)
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (GaussianRationalL1.qL1_represents q a D hD hq) (fraction_represents A D hD) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq hA]

theorem coefficient_norm (k : PTm n) : Γ ⊢[PRAAx] qL1 (coefficient k) ≐ fraction one (succ k) :=
  l1_from_representation _ _ _ _ (zero_lt_succ k) (GaussianFiniteLogarithmPolynomial.coefficient_represents k) (sign_norm1 k)

theorem radius_power_norm (A B e : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qL1 (power (radiusPoint A B) e) ≐ fraction (pw A e) (pw B e) :=
  l1_from_representation _ _ _ _ (GaussianFactorBudget.power_positive B e hB)
    (GaussianDominantPairAlgebra.radius_power_represents A B e hB) (radius_norm1 (pw A e))

theorem coefficient_power_bound (A B k e : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qmul (coefficient k) (power (radiusPoint A B) e)))
      (fraction (pw A e) (succ k*pw B e)) := by
  have factor := (RationalAlgebra.multiply_congr (coefficient_norm (Γ := Γ) k) (radius_power_norm A B e hB)).eqTrans
    ((RationalNonnegativePowers.fraction_multiply one (succ k) (pw A e) (pw B e)
      (zero_lt_succ k) (GaussianFactorBudget.power_positive B e hB)).eqTrans
        (RationalNonnegativePowers.fraction_congr (one_mul _) (.eqRefl _)))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) factor (GaussianRationalL1Algebra.qL1_multiply _ _)

def point : PTm n := radiusPoint (num 5) (num 9)
def buffer (d : PTm n) : PTm n := GaussianRationalPolynomialDilation.dilated (polynomial d) d point
def majorant (e : PTm n) : PTm n := fraction (pw (num 5) (succ e)) (num 8*pw (num 9) e)
ipra_subst point
ipra_subst buffer
ipra_subst majorant

theorem nine_positive : Γ ⊢[PRAAx] le one (num 9 : PTm n) := le_of_eq_add (d := num 8) (by ipra_ring)
theorem eight_positive : Γ ⊢[PRAAx] le one (num 8 : PTm n) := le_of_eq_add (d := num 7) (by ipra_ring)
theorem den_positive (e : PTm n) : Γ ⊢[PRAAx] le one (num 8*pw (num 9) e) :=
  GaussianRationalHorner.positive_product _ _ eight_positive (GaussianFactorBudget.power_positive _ _ nine_positive)

theorem entry_at (d i : PTm n) (hi : Γ ⊢[PRAAx] le i d) : Γ ⊢[PRAAx]
    entry (buffer d) i ≐ qmul (GaussianFiniteLogarithmPolynomial.sourceCoefficient (monus d i)) (power point (monus d i)) :=
  (GaussianRationalPolynomialDilation.dilated_lookup _ d point i hi).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (GaussianFiniteLogarithmPolynomial.polynomial_lookup d i hi) (.eqRefl _))

theorem high_coefficient_bound (e : PTm n) (he : Γ ⊢[PRAAx] le two e) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qmul (GaussianFiniteLogarithmPolynomial.sourceCoefficient e) (power point e)))
      (fraction (pw (num 5) e) (two*pw (num 9) e)) := by
  have h1 : Γ ⊢[PRAAx] le one e := le_trans (le_succ_self one) he
  have shape := RationalIntegerNormalization.positive_form h1
  have source := (GaussianFiniteLogarithmPolynomial.source_congr shape).eqTrans
    (GaussianFiniteLogarithmPolynomial.source_succ (PTm.pred e))
  have first := RationalArgmin.rationalLE_congr
    (GaussianCoefficientL1.qL1_congr (GaussianRationalSyntheticDivision.qmul_congr source.eqSymm (.eqRefl _)))
    (RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrMul shape.eqSymm (.eqRefl _)))
      (coefficient_power_bound (num 5) (num 9) (PTm.pred e) e nine_positive)
  have hp := GaussianFactorBudget.power_positive (Γ := Γ) (num 9) e nine_positive
  have comparison := GaussianEuclideanDistanceName.fraction_order (pw (num 5) e) (e*pw (num 9) e)
    (pw (num 5) e) (two*pw (num 9) e)
    (GaussianRationalHorner.positive_product _ _ h1 hp) (GaussianRationalHorner.positive_product _ _ (le_succ_self one) hp)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (pw (num 9) e*pw (num 5) e) he))
  exact RationalArgmin.transitive first comparison

theorem majorant_step (e : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.add (majorant (succ e)) (fraction (pw (num 5) (succ e)) (two*pw (num 9) (succ e))) ≐ majorant e := by
  have hp := GaussianFactorBudget.power_positive (Γ := Γ) (num 9) (succ e) nine_positive
  have hd := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (le_succ_self one) hp
  have hsum := RationalRepresentations.represents_add (Γ := Γ) (majorant (succ e))
    (fraction (pw (num 5) (succ e)) (two*pw (num 9) (succ e)))
    (ZT.ofNat (pw (num 5) (succ (succ e)))) (ZT.ofNat (pw (num 5) (succ e)))
    (num 8*pw (num 9) (succ e)) (two*pw (num 9) (succ e))
    (fraction_represents _ _ (den_positive (succ e))) (fraction_represents _ _ hd)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (den_positive e)) hsum
    (fraction_represents _ _ (den_positive e))
    (GaussianRationalHorner.positive_product _ _ (den_positive (succ e)) hd) (den_positive e)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  rw [natEq (pw_succ (Γ := Γ) (num 5) (succ e)),natEq (pw_succ (Γ := Γ) (num 9) e)]
  ipra_simps
  ring

def prefixLaw (d i : PTm n) : Fm PTm n := le (succ i) d ⟶ rationalLE (prefixNorm (buffer d) i) (majorant (monus d i))
ipra_subst prefixLaw

theorem prefix_zero (d : PTm n) : Γ ⊢[PRAAx] prefixLaw d zero := by
  refine .impI ?_
  exact RationalArgmin.rationalLE_congr
    ((GaussianCoefficientL1.prefix_zero _).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm).eqSymm
    (.eqRefl _)
    (GaussianEuclideanDistanceName.fraction_order zero one (pw (num 5) (succ (monus d zero)))
      (num 8*pw (num 9) (monus d zero)) (le_refl _) (den_positive _)
        (le_congr (mul_zero _).eqSymm (by ipra_ring) (zero_le _)))

theorem prefix_step (d i : PTm n) (hi : Γ ⊢[PRAAx] le (succ (succ i)) d)
    (ih : Γ ⊢[PRAAx] prefixLaw d i) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer d) (succ i)) (majorant (monus d (succ i))) := by
  have prev : Γ ⊢[PRAAx] le (succ i) d := le_trans (le_succ_self _) hi
  have old := Prf.impE ih prev
  have rem : Γ ⊢[PRAAx] monus d i ≐ succ (monus d (succ i)) :=
    (GaussianRationalPowerExpansion.remaining_succ d i).eqSymm.eqTrans
      (GaussianRationalPowerExpansion.remaining_before d (succ i) prev)
  have e2 : Γ ⊢[PRAAx] le two (monus d i) := by
    apply le_of_eq_add (d := monus d (succ (succ i)))
    ipra_lc natEq (eq_add_of_le hi)-natEq (eq_add_of_le (le_trans (le_succ_self i) prev))
  have hEntry := RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr (entry_at d i (le_trans (le_succ_self i) prev))).eqSymm
    (.eqRefl _) (high_coefficient_bound (monus d i) e2)
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ old hEntry
  have hRem := congrAp2 powF rem (.eqRefl (num 5))
  have termEq : Γ ⊢[PRAAx] fraction (pw (num 5) (monus d i)) (two*pw (num 9) (monus d i)) ≐
      fraction (pw (num 5) (succ (monus d (succ i)))) (two*pw (num 9) (succ (monus d (succ i)))) :=
    RationalNonnegativePowers.fraction_congr hRem (congrMul (.eqRefl _) (congrAp2 powF rem (.eqRefl _)))
  have budgetEq : Γ ⊢[PRAAx] majorant (monus d i) ≐ majorant (succ (monus d (succ i))) := by
    ipra_congr (majorant (var 0) : PTm 1) with [rem]
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.prefix_succ _ _).eqSymm
    ((RationalAlgebra.add_congr budgetEq termEq).eqTrans (majorant_step (monus d (succ i)))) added

theorem prefix_bound (d i : PTm n) (hi : Γ ⊢[PRAAx] le (succ i) d) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer d) i) (majorant (monus d i)) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift d) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixLaw]
    · exact prefix_zero d
    · exact .impI (prefix_step _ _ Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] prefixLaw d i := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem majorant_one : Γ ⊢[PRAAx] majorant (one : PTm n) ≐ fraction (num 25) (num 72) := by
  have a : Γ ⊢[PRAAx] pw (num 5) (succ one) ≐ num 25 :=
    (pw_succ (num 5) one).eqTrans ((congrMul (pw_one (num 5)) (.eqRefl _)).eqTrans (by ipra_ring))
  have b : Γ ⊢[PRAAx] num 8*pw (num 9) one ≐ num 72 :=
    (congrMul (.eqRefl _) (pw_one (num 9))).eqTrans (by ipra_ring)
  exact RationalNonnegativePowers.fraction_congr a b

theorem high_prefix (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer d) (monus d one)) (fraction (num 25) (num 72)) := by
  have shape : Γ ⊢[PRAAx] succ (monus d one) ≐ d :=
    (show Γ ⊢[PRAAx] succ (monus d one) ≐ one+monus d one by ipra_ring).eqTrans (eq_add_of_le hd).eqSymm
  have bound : Γ ⊢[PRAAx] le (succ (monus d one)) d := le_congr (.eqRefl _) shape (le_refl _)
  have normalized : Γ ⊢[PRAAx] majorant (monus d (monus d one)) ≐ majorant one := by
    ipra_congr (majorant (var 0) : PTm 1) with [GaussianRationalMonicReconstruction.complement d one hd]
  have majorantEq := normalized.eqTrans majorant_one
  exact RationalArgmin.rationalLE_congr (.eqRefl _) majorantEq (prefix_bound d _ bound)

theorem linear_entry (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (buffer d) (monus d one))) (fraction (num 5) (num 9)) := by
  have e := GaussianRationalMonicReconstruction.complement (Γ := Γ) d one hd
  have value := (entry_at d (monus d one) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr
      ((GaussianFiniteLogarithmPolynomial.source_congr e).eqTrans (GaussianFiniteLogarithmPolynomial.source_succ zero))
      (congrAp2 GaussianRationalReciprocal.powerF e (.eqRefl _)))
  have rhs : Γ ⊢[PRAAx] fraction (pw (num 5) one) (succ zero*pw (num 9) one) ≐ fraction (num 5) (num 9) :=
    RationalNonnegativePowers.fraction_congr (pw_one _)
      ((congrMul (.eqRefl _) (pw_one _)).eqTrans (one_mul _))
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr value).eqSymm rhs
    (coefficient_power_bound (num 5) (num 9) zero one nine_positive)

theorem small_sum : Γ ⊢[PRAAx]
    RationalArithmetic.add (fraction (num 25) (num 72)) (fraction (num 5) (num 9)) ≐ fraction (num 65) (num 72) := by
  have h72 : Γ ⊢[PRAAx] le one (num 72 : PTm n) := le_of_eq_add (d := num 71) (by ipra_ring)
  have rep := RationalRepresentations.represents_add (Γ := Γ)
    (fraction (num 25) (num 72)) (fraction (num 5) (num 9)) (ZT.ofNat (num 25)) (ZT.ofNat (num 5)) (num 72) (num 9)
    (fraction_represents _ _ h72) (fraction_represents _ _ nine_positive)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ h72) rep (fraction_represents _ _ h72)
    (GaussianRationalHorner.positive_product _ _ h72 nine_positive) h72
  ipra_lc

theorem through_linear (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer d) d) (fraction (num 65) (num 72)) := by
  have shape : Γ ⊢[PRAAx] succ (monus d one) ≐ d :=
    (show Γ ⊢[PRAAx] succ (monus d one) ≐ one+monus d one by ipra_ring).eqTrans (eq_add_of_le hd).eqSymm
  have step : Γ ⊢[PRAAx] prefixNorm (buffer d) d ≐
      RationalArithmetic.add (prefixNorm (buffer d) (monus d one)) (qL1 (entry (buffer d) (monus d one))) :=
    (GaussianCoefficientNormOrder.prefixNorm_congr (.eqRefl _) shape.eqSymm).eqTrans
      (GaussianCoefficientL1.prefix_succ _ _)
  exact RationalArgmin.rationalLE_congr step.eqSymm small_sum
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (high_prefix d hd) (linear_entry d hd))

theorem constant_entry (d : PTm n) : Γ ⊢[PRAAx]
    qL1 (entry (buffer d) d) ≐ GaussianRationalSyntheticBounds.natCode zero :=
  (GaussianCoefficientL1.qL1_congr ((entry_at d d (le_refl _)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr
      ((GaussianFiniteLogarithmPolynomial.source_congr (monus_self d)).eqTrans GaussianFiniteLogarithmPolynomial.source_zero)
      (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)))).eqTrans
        GaussianRationalLinearProduct.qzero_norm

theorem constant_removed (d : PTm n) : Γ ⊢[PRAAx] coefficientNorm (buffer d) ≐ prefixNorm (buffer d) d :=
  (GaussianRationalLinearProduct.norm_length _ _ (GaussianRationalPolynomialDilation.dilated_length _ _ _)).eqTrans
    ((GaussianCoefficientL1.prefix_succ _ _).eqTrans
      ((RationalAlgebra.add_congr (.eqRefl _) (constant_entry d)).eqTrans
        (GaussianRationalLinearProduct.scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))))

/-- Original H_d has a uniform auxiliary-radius weighted coefficient norm,
including the zero-degree computation; the budget is derived, not input. -/
theorem logarithm_bound (d : PTm n) : Γ ⊢[PRAAx]
    rationalLE (GaussianRationalPolynomialDilation.weightedNorm (polynomial d) d point) (fraction (num 65) (num 72)) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have small : ((d ≐ zero) :: Γ) ⊢[PRAAx]
        prefixNorm (buffer d) d ≐ fraction zero one :=
      (GaussianCoefficientNormOrder.prefixNorm_congr (.eqRefl _) Prf.hyp0).eqTrans
        ((GaussianCoefficientL1.prefix_zero _).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm)
    have h72 : ((d ≐ zero) :: Γ) ⊢[PRAAx] le one (num 72 : PTm n) := le_of_eq_add (d := num 71) (by ipra_ring)
    exact RationalArgmin.rationalLE_congr ((constant_removed d).eqTrans small).eqSymm (.eqRefl _)
      (GaussianEuclideanDistanceName.fraction_order zero one (num 65) (num 72) (le_refl _) h72
        (le_congr (mul_zero _).eqSymm (by ipra_ring) (zero_le (num 65))))
  · have h1 : ((d ≐ succ (PTm.pred d)) :: Γ) ⊢[PRAAx] le one d :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_of_eq_add (d := PTm.pred d) (by ipra_ring))
    exact RationalArgmin.rationalLE_congr (constant_removed d).eqSymm (.eqRefl _) (through_linear d h1)

/-! Actual PR1 output retains the original H_d, its real weighted buffer,
the computed rational norm and the actual auxiliary-radius point. -/
def output (d : PTm n) : PTm n := pairT (polynomial d)
  (pairT (buffer d) (pairT (GaussianRationalPolynomialDilation.weightedNorm (polynomial d) d point) point))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (d : PTm n) : PTm n := ap1 outputF d
ipra_subst output
ipra_subst run
theorem program_at (d : PTm n) : Γ ⊢[PRAAx] run d ≐ output d := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![d]
theorem returned_polynomial (d : PTm n) : Γ ⊢[PRAAx] fstT (run d) ≐ polynomial d :=
  (program_at d).fstE
theorem returned_tail (d : PTm n) : Γ ⊢[PRAAx] sndT (run d) ≐
    pairT (buffer d) (pairT (GaussianRationalPolynomialDilation.weightedNorm (polynomial d) d point) point) :=
  (program_at d).sndE
theorem returned_buffer (d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d)) ≐ buffer d :=
  (returned_tail d).fstE
theorem returned_pair (d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d)) ≐
    pairT (GaussianRationalPolynomialDilation.weightedNorm (polynomial d) d point) point :=
  (returned_tail d).sndE
theorem returned_norm (d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d))) ≐
    GaussianRationalPolynomialDilation.weightedNorm (polynomial d) d point :=
  (returned_pair d).fstE
theorem returned_point (d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d))) ≐ (point : PTm n) :=
  (returned_pair d).sndE
theorem returned_bound (d : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run d)))) (fraction (num 65) (num 72)) :=
  RationalArgmin.rationalLE_congr (returned_norm d).eqSymm (.eqRefl _) (logarithm_bound d)

theorem actual_logarithm_coefficient_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qL1 (coefficient (var 0)) ≐ fraction one (succ (var 0))) := closeUniv 1 (coefficient_norm _)
theorem actual_positive_axis_power_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ qL1 (power (radiusPoint (var 0) (var 1)) (var 2)) ≐
      fraction (pw (var 0) (var 2)) (pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (radius_power_norm _ _ _ Prf.hyp0))
theorem actual_logarithm_power_term_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE (qL1 (qmul (coefficient (var 2)) (power (radiusPoint (var 0) (var 1)) (var 3))))
      (fraction (pw (var 0) (var 3)) (succ (var 2)*pw (var 1) (var 3)))) :=
  closeUniv 4 (.impI (coefficient_power_bound _ _ _ _ Prf.hyp0))
theorem actual_high_coefficient_prefix_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (succ (var 1)) (var 0) ⟶ rationalLE (prefixNorm (buffer (var 0)) (var 1))
      (majorant (monus (var 0) (var 1)))) := closeUniv 2 (.impI (prefix_bound _ _ Prf.hyp0))
theorem actual_auxiliary_logarithm_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (rationalLE (GaussianRationalPolynomialDilation.weightedNorm (polynomial (var 0)) (var 0) point)
      (fraction (num 65) (num 72))) := closeUniv 1 (logarithm_bound _)
theorem actual_auxiliary_logarithm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)
theorem returned_auxiliary_logarithm_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (rationalLE (fstT (sndT (sndT (run (var 0))))) (fraction (num 65) (num 72))) := closeUniv 1 (returned_bound _)
theorem returned_auxiliary_logarithm_sources_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((fstT (run (var 0)) ≐ polynomial (var 0)) ⋏ ((fstT (sndT (run (var 0))) ≐ buffer (var 0)) ⋏
      (sndT (sndT (sndT (run (var 0)))) ≐ (point : PTm 1)))) :=
  closeUniv 1 (.andI (returned_polynomial _) (.andI (returned_buffer _) (returned_point _)))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmWeightedNorm
