import IPRADerivations.Analysis.GaussianGammaOriginalPrefixCoefficientVariation
import IPRADerivations.Analysis.GaussianFiniteSumL1Variation

/-!
# Actual original C19 prefix-evaluation regularity

The unchanged original prefixValue sums its SAME cofinal whole-polynomial
coefficients. Their computed common modulus and the original query disk
give one explicit modulus for the whole actual finite power prefix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixRegularity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaOriginalC19Prefix (buffer totalDegree prefixValue)
open GaussianGammaOriginalPrefixCoefficientVariation (cap original_reader_distance)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power)
open GaussianRationalL1 (qL1)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianCoefficientL1 (qL1_congr)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalSyntheticBounds (natCode)
open GaussianGammaCanonicalExponent (source)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termData (q z R B d : PTm n) : PTm n := GaussianRationalPowerExpansion.data
  (buffer q R d) (totalDegree q R d) (ofGaussian z B)
def sourceTerm (q z R B d e : PTm n) : PTm n := GaussianOffDominantTerms.term
  (buffer q R d) (totalDegree q R d) (ofGaussian z B) e
def termModulus (R d : PTm n) : PTm n := (two*two)*cap R d*pw R d
def modulus (R d : PTm n) : PTm n := succ d*termModulus R d
@[simp] theorem subst_termData {l : ℕ} (σ : Fin n → PTm l) (q z R B d : PTm n) :
    Syn.subst σ (termData q z R B d) = termData (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [termData,buffer,totalDegree,GaussianGammaOriginalC19Prefix.stage,GaussianGammaCofinalCoefficientName.coefficientPrecision,
    GaussianGammaCofinalCoefficientName.degreeCutoff,GaussianGammaCofinalCoefficientName.exponentialCutoff,
    GaussianGammaCofinalCoefficientName.exponentClock,GaussianGammaCofinalCoefficientName.inputClock,GaussianGammaCofinalCoefficientName.outerClock]
@[simp] theorem subst_sourceTerm {l : ℕ} (σ : Fin n → PTm l) (q z R B d e : PTm n) :
    Syn.subst σ (sourceTerm q z R B d e) = sourceTerm (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ e) := by
  simp [sourceTerm,buffer,totalDegree,GaussianGammaOriginalC19Prefix.stage,GaussianGammaCofinalCoefficientName.coefficientPrecision,
    GaussianGammaCofinalCoefficientName.degreeCutoff,GaussianGammaCofinalCoefficientName.exponentialCutoff,
    GaussianGammaCofinalCoefficientName.exponentClock,GaussianGammaCofinalCoefficientName.inputClock,GaussianGammaCofinalCoefficientName.outerClock]
@[simp] theorem subst_termModulus {l : ℕ} (σ : Fin n → PTm l) (R d : PTm n) :
    Syn.subst σ (termModulus R d) = termModulus (Syn.subst σ R) (Syn.subst σ d) := by simp [termModulus]
@[simp] theorem subst_modulus {l : ℕ} (σ : Fin n → PTm l) (R d : PTm n) :
    Syn.subst σ (modulus R d) = modulus (Syn.subst σ R) (Syn.subst σ d) := by simp [modulus]

theorem term_as_reader (q z R B d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    sourceTerm q z R B d e ≐ qmul (exponentCoefficient (buffer q R d) (totalDegree q R d) e) (power (ofGaussian z B) e) :=
  qmul_congr (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _
    (le_trans he (GaussianGammaOriginalC19Prefix.degree_dominates q R d))).eqSymm (.eqRefl _)

theorem source_term_at (q z R B d e : PTm n) : Γ ⊢[PRAAx]
    inst2 GaussianRationalPowerExpansion.termBody e (termData q z R B d) ≐ sourceTerm q z R B d e :=
  GaussianRationalPowerExpansion.term_body_at _ _ _ _

theorem query_power_bound (z R B d e : PTm n) (h : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    bounded (power (ofGaussian z B) e) (pw R d) one := by
  have original : Γ ⊢[PRAAx] bounded (power (ofGaussian z B) e) (pw R e) one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power e)
      (GaussianRationalReciprocal.bounded_power _ R one e (le_refl one) (GaussianGammaSynchronousExponentName.query_bound z R B h))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (GaussianFactorBudget.power_monotone_length R e d h.andE₁ he)) original

theorem term_error (p q z R B d e : PTm n) (h : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (sourceTerm p z R B d e) (sourceTerm q z R B d e)))
      (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) := by
  have powerNorm : Γ ⊢[PRAAx] rationalLE (qL1 (power (ofGaussian z B) e)) (natCode (two*pw R d)) :=
    GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl one) (query_power_bound z R B d e h he)
  have coefficientNorm := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (denominator_positive (Γ := Γ) p q)
    (original_reader_distance p q R d e h.andE₁ he)
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) _ _)
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
      (GaussianRationalSyntheticBounds.natCode_nonnegative _) powerNorm coefficientNorm)
  have code : Γ ⊢[PRAAx] qsub (sourceTerm p z R B d e) (sourceTerm q z R B d e) ≐
      qmul (power (ofGaussian z B) e)
        (qsub (exponentCoefficient (buffer p R d) (totalDegree p R d) e)
          (exponentCoefficient (buffer q R d) (totalDegree q R d) e)) :=
    (qsub_congr (term_as_reader p z R B d e he) (term_as_reader q z R B d e he)).eqTrans
      ((qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
        (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _))
  have budgetCode : Γ ⊢[PRAAx] multiply (natCode (two*pw R d))
      (fraction (two*(cap R d*radiusNumerator p q)) (radiusDenominator p q)) ≐
      fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold termModulus; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (qL1_congr code).eqSymm budgetCode product

theorem original_sum_binding (q z R B d : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ d) (termData q z R B d) ≐ prefixValue q z R B d :=
  GaussianRationalFiniteSum.generated_prefix_congr GaussianRationalPowerExpansion.termBody
    (succ d) (succ (totalDegree q R d)) (termData q z R B d) (succ d) (le_refl _)
      ((succ_monus_succ _ _).eqTrans (GaussianGammaOriginalC19Prefix.degree_dominates q R d))

theorem original_sum_error (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ d) (termData p z R B d))
      (GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ d) (termData q z R B d))))
        (fraction (modulus R d*radiusNumerator p q) (radiusDenominator p q)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError GaussianRationalPowerExpansion.termBody
      GaussianRationalPowerExpansion.termBody (succ d) (termData p z R B d) (termData q z R B d)
        (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
    have actual := RationalArgmin.rationalLE_congr
      (qL1_congr (qsub_congr
        (source_term_at (Γ := Δ) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift d) (var 0))
        (source_term_at (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift d) (var 0)))).eqSymm
      (.eqRefl _) (term_error (Syn.shift p) (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift d) (var 0)
        hs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
    simpa only [Δ,Syn.shift,subst_termData,GaussianEuclideanDistanceName.subst_fraction,subst_termModulus,
      GaussianGammaInputPrecisionNorm.subst_radiusNumerator,GaussianGammaInputPrecisionNorm.subst_radiusDenominator,
      PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using actual
  have code : Γ ⊢[PRAAx] multiply (natCode (succ d)) (fraction (termModulus R d*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (modulus R d*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold modulus; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) code (GaussianFiniteSumL1Variation.sum_error _ _ _ _ _ _ terms)

theorem original_prefix_regularity (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (prefixValue p z R B d) (prefixValue q z R B d)
      (modulus R d*radiusNumerator p q) (radiusDenominator p q) := by
  have metric := GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (denominator_positive p q)
    (original_sum_error p q z R B d h)
  exact GaussianRationalReciprocal.bound_congr (qsub_congr (original_sum_binding p z R B d) (original_sum_binding q z R B d))
    (.eqRefl _) (.eqRefl _) metric

theorem original_actual_C19_prefix_regularity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded
      (prefixValue (var 0) (var 2) (var 3) (var 4) (var 5)) (prefixValue (var 1) (var 2) (var 3) (var 4) (var 5))
        (modulus (var 3) (var 5)*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_prefix_regularity _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixRegularity
