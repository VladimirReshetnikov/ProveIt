import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalChordInverse
import IPRADerivations.Analysis.Polynomials.GaussianNamedConstantCoefficientDifferenceProduct

/-!
# Product rule for the original negative Gamma thin-chord quotient

The same actual finite inverse shift product gives the negative Gamma
factorization at the base and at the chord center. Translating both input
numerators by the common denominator leaves the signed rational increment
unchanged and identifies the positive quotient in the product rule.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaInputProperness (code_data_cross)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator increment center_source)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalChordInverse (centerInverse finiteInverseCoefficient exact_inverse_step)
open GaussianGammaNegativeIntervalChordStep (center_guard quotientData)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse liftedF liftedData lifted_regular original_inverse_product)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addData multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedConstantCoefficientDifferenceProduct (lhsF lhsData rhsF rhsData product_rule rhs_regular)
open GaussianNamedDifferenceQuotient (separated)
open GaussianRationalReciprocal (reciprocalF reciprocal_program)
open GaussianRootAlgebra (equal equal_of_values normSq_equal)
open GaussianStirlingGammaLogarithm (gammaData gamma_regular)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "QD" => GaussianNamedDifferenceQuotient.data gammaF gammaF
local notation "GD" => GaussianGammaNegativeIntervalNative.data

def finiteF : PR 2 := rhsF gammaF gammaF
def finiteData (a c b N W : PTm n) : PTm n :=
  rhsData gammaF gammaF (centerInverse a c b N W) (finiteInverseCoefficient a c b N W)
    (gammaData (centerNumerator (b+a) (b+c) W) (centerDenominator b W)) (gammaData (b+a) b)
    (increment (b+a) (b+c)) (centerDenominator b W)

@[simp] theorem subst_finiteData {k : ℕ} (σ : Fin n → PTm k) (a c b N W : PTm n) :
    Syn.subst σ (finiteData a c b N W) =
      finiteData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ W) := by
  simp [finiteData, centerInverse, finiteInverseCoefficient, GaussianGammaNegativeIntervalChordInverse.shiftCoefficient]

theorem translated_increment (a c b : PTm n) : Γ ⊢[PRAAx] equal (increment a c) (increment (b+a) (b+c)) := by
  apply equal_of_values
  · simp only [increment, ComplexLogarithmRemainder.eval_re_code]
    simp only [ZT.toZ]
    ipra_simps
    ring
  · simp only [increment, ComplexLogarithmRemainder.eval_im_code, ZT.toZ_ofNat]

theorem translated_center (a c b W : PTm n) (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx]
    centerDenominator b W+centerNumerator a c W ≐ centerNumerator (b+a) (b+c) W := by
  have eq := natEq (GaussianOffDominantWeights.positive_succ_pred W hw)
  unfold centerDenominator centerNumerator
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(b)*eq

theorem translated_apart (a c b : PTm n) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] lt (b+a) (b+c) ⋎ lt (b+c) (b+a) := by
  have move {Δ : List (Fm PTm n)} (x y : PTm n) (h : Δ ⊢[PRAAx] lt x y) : Δ ⊢[PRAAx] lt (b+x) (b+y) :=
    le_congr (by ipra_ring) (add_comm y b) (add_le_add_right b h)
  exact .orE apart (.orI₁ (move a c Prf.hyp0)) (.orI₂ (move c a Prf.hyp0))

theorem positive_center_regular (a c b W : PTm n) (hc : Γ ⊢[PRAAx] guard c b) (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] pointCN gammaF (gammaData (centerNumerator (b+a) (b+c) W) (centerDenominator b W)) := by
  have hs := shifted_source c b hc
  exact gamma_regular _ _ (center_source _ _ _ _ hs.andE₁ hs.andE₂ hw)

theorem lifted_center_cross (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx]
    crossEquivalent gammaF liftedF (GD (centerNumerator a c W) (centerDenominator b W) N)
      (multiplyData constantF gammaF (centerInverse a c b N W)
        (gammaData (centerNumerator (b+a) (b+c) W) (centerDenominator b W))) := by
  let A := centerNumerator a c W
  let B := centerDenominator b W
  let T := centerNumerator (b+a) (b+c) W
  let C := centerInverse a c b N W
  have hn := center_guard a c b W ha hc hw
  have code : Γ ⊢[PRAAx] gammaData (B+A) B ≐ gammaData T B := by
    simpa only [GaussianStirlingGammaLogarithm.subst_gammaData, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
      Prf.eqCongr (gammaData (var 0) (var 1) : PTm 2) (σ := ![B+A,B]) (σ' := ![T,B])
        (fun j => by fin_cases j; exact translated_center a c b W hw; exact .eqRefl B)
  have p := gamma_regular _ _ (shifted_source A B hn)
  have q := positive_center_regular a c b W hc hw
  have reg := constant_regular (Γ := Γ) C
  have reindex := multiply_cross constantF constantF gammaF gammaF C C (gammaData (B+A) B) (gammaData T B)
    reg reg p q (cross_refl _ _ reg) (code_data_cross gammaF _ _ p q code)
  exact cross_trans _ _ _ _ _ _ (original_inverse_product A B N hn) reindex

private theorem positive_quotient_code (a c b W : PTm n) (hd : Γ ⊢[PRAAx] le one (centerDenominator b W)) :
    Γ ⊢[PRAAx]
    QD (gammaData (centerNumerator (b+a) (b+c) W) (centerDenominator b W)) (gammaData (b+a) b)
        (increment a c) (centerDenominator b W) ≐
      GaussianGammaMinimumSignedStep.quotientData (b+a) (b+c) b W := by
  let D := centerDenominator b W
  let I := GaussianNamedDifferenceQuotient.inverse (increment a c) D
  let J := GaussianNamedDifferenceQuotient.inverse (increment (b+a) (b+c)) D
  let x := gammaData (centerNumerator (b+a) (b+c) W) D
  let y := gammaData (b+a) b
  let d := GaussianNamedDifference.data x y
  have eq := GaussianGammaFiniteValueProperness.fraction_equal _ _ D hd (translated_increment a c b)
  have he : Γ ⊢[PRAAx] I ≐ J :=
    (reciprocal_program _).eqSymm.eqTrans ((congrAp1 reciprocalF eq).eqTrans (reciprocal_program _))
  change Γ ⊢[PRAAx] multiplyData constantF (GaussianNamedDifference.nameF gammaF gammaF) I d ≐
    multiplyData constantF (GaussianNamedDifference.nameF gammaF gammaF) J d
  simpa only [GaussianNameArithmetic.subst_multiplyData, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Prf.eqCongr (multiplyData constantF (GaussianNamedDifference.nameF gammaF gammaF) (var 0) (var 1) : PTm 2)
      (σ := ![I,d]) (σ' := ![J,d]) (fun j => by fin_cases j; exact he; exact .eqRefl d)

private theorem shifted_separated (a c b W : PTm n) (sep : Γ ⊢[PRAAx] separated (increment a c) (centerDenominator b W)) :
    Γ ⊢[PRAAx] separated (increment (b+a) (b+c)) (centerDenominator b W) :=
  .andI sep.andE₁ (le_congr (.eqRefl _) (normSq_equal (translated_increment a c b)) sep.andE₂)

theorem finite_regular (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] pointCN finiteF (finiteData a c b N W) := by
  have h := GaussianGammaNegativeIntervalChordStep.quotient_input a c b N W ha hc hw apart
  exact rhs_regular gammaF gammaF _ _ _ _ _ _ (positive_center_regular a c b W hc hw)
    (gamma_regular _ _ (shifted_source a b ha)) (shifted_separated a c b W h.andE₂.andE₂)

theorem quotient_cross (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] crossEquivalent QF finiteF (quotientData a c b N W) (finiteData a c b N W) := by
  let A := centerNumerator a c W
  let D := centerDenominator b W
  let C₁ := centerInverse a c b N W
  let C₀ := inverse a b N
  let CΔ := finiteInverseCoefficient a c b N W
  let x := gammaData (centerNumerator (b+a) (b+c) W) D
  let y := gammaData (b+a) b
  let h := increment a c
  have hs := GaussianGammaNegativeIntervalChordStep.quotient_input a c b N W ha hc hw apart
  have hx := positive_center_regular a c b W hc hw
  have hy := gamma_regular _ _ (shifted_source a b ha)
  have sep := hs.andE₂.andE₂
  have eq : Γ ⊢[PRAAx] crossEquivalent QF (lhsF gammaF gammaF) (quotientData a c b N W)
      (lhsData gammaF gammaF C₁ C₀ x y h D) :=
    GaussianNamedDifferenceQuotientProperness.proper gammaF liftedF gammaF liftedF (GD A D N)
      (multiplyData constantF gammaF C₁ x) (GD a b N) (liftedData a b N) h D
      hs.andE₁ (multiply_fast _ _ _ _ (constant_regular C₁) hx) hs.andE₂.andE₁ (lifted_regular a b N ha)
      (lifted_center_cross a c b N W ha hc hw) (original_inverse_product a b N ha)
  have rule := product_rule gammaF gammaF C₁ C₀ CΔ x y h D hx hy sep (exact_inverse_step a c b N W ha hc hw)
  let q := QD x y h D
  let q' := GaussianGammaMinimumSignedStep.quotientData (b+a) (b+c) b W
  let tail := multiplyData constantF gammaF CΔ y
  have code : Γ ⊢[PRAAx] rhsData gammaF gammaF C₁ CΔ x y h D ≐ finiteData a c b N W := by
    change Γ ⊢[PRAAx] addData (multiplyData constantF QF C₁ q) tail ≐ addData (multiplyData constantF QF C₁ q') tail
    simpa only [GaussianNameArithmetic.subst_addData, GaussianNameArithmetic.subst_multiplyData,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (addData (multiplyData constantF QF (var 0) (var 1)) (var 2) : PTm 3)
        (σ := ![C₁,q,tail]) (σ' := ![C₁,q',tail])
        (fun j => by fin_cases j; exact .eqRefl C₁; exact positive_quotient_code a c b W sep.andE₁; exact .eqRefl tail)
  exact cross_trans _ _ _ _ _ _ eq (cross_trans _ _ _ _ _ _ rule
    (code_data_cross finiteF _ _ (rhs_regular gammaF gammaF _ _ _ _ _ _ hx hy sep)
      (finite_regular a c b N W ha hc hw apart) code))

theorem actual_original_negative_Gamma_chord_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((guard (var 0) (var 2) ⋏ (guard (var 1) (var 2) ⋏ (le one (var 4) ⋏ (lt (var 0) (var 1) ⋎ lt (var 1) (var 0))))) ⟶
      crossEquivalent QF finiteF (quotientData (var 0) (var 1) (var 2) (var 3) (var 4))
        (finiteData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (quotient_cross _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordQuotient
