import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedMajorantExponent
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaLogHarmonicName

/-!
# The sharp folded Euler exponent with the original fixed Euler name

The actual constructor is (gamma_N-H_(2R))z/B+T_(2R)-T_N.
It retains the fixed Euler observations, all original tail observations,
and all actual operation clocks. Original source guards derive the raw
A+2^(-p) envelope, A=2R^2+2R; exact disk shrinking produces an equivalent
regular name with the precise A disk. Identification with original Q_N
is a separate consumer, not an assumption of these estimates.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFixedEulerExponent

open_ipra
open GaussianRationalPowerDifference (bounded_sum_one)
open GaussianRationalHorner (positive_product ofGaussian)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_product bounded_negative)
open GaussianGammaCanonicalExponent (source constantF constant_regular constant_at harmonicPoint addPrecision)
open GaussianGammaLogHarmonicName (fixedF fixed_regular)
open GaussianGammaFoldedMajorantExponent (input tail_source later_tail_half_bound
  combined_point_bound_of_exponent envelope_of_sample_bound corrected_exponential_input_of_envelope)
open GaussianGammaCanonicalExponentBound (numericalRadius harmonic_point_bound numerator_range scalar_representation_bound)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianFastValueCut (rawEnvelope)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differenceF : PR 2 := GaussianNameArithmetic.addF fixedF constantF
def differenceData (K N : PTm n) : PTm n := GaussianNameArithmetic.addData N (qnegative (harmonicPoint K))
def productF : PR 2 := GaussianNameArithmetic.multiplyF differenceF constantF
def productData (z B K N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData differenceF constantF
  (differenceData K N) (ofGaussian z B)
def exponentF : PR 2 := GaussianNameArithmetic.addF productF GaussianGammaCanonicalTailName.pointF
def exponentData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData
  (productData z B (two*R) N) (GaussianGammaCanonicalTailName.data z R B (two*R))
ipra_subst differenceData
ipra_subst productData
ipra_subst exponentData

theorem fixed_sample_bound (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (ap2 fixedF p N) one one := by
  let q := GammaEulerConstantName.fixedSample p N
  have inside := GammaEulerConstantName.fixed_sample_range (Γ := Γ) p N hN
  have bounds := numerator_range q one inside.andE₁ inside.andE₂
  exact bound_congr (RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.fixedF p N).eqSymm (.eqRefl _) (.eqRefl _)
    (scalar_representation_bound q one (RationalSupMetric.denominatorOf q) (RationalSupMetric.numeratorOf q)
      (RationalArgmin.denominator_positive q) (RationalRepresentations.represents_self q) bounds.andE₁ bounds.andE₂)

theorem difference_regular (K N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN differenceF (differenceData K N) :=
  GaussianNameArithmetic.add_fast fixedF constantF N (qnegative (harmonicPoint K)) (fixed_regular N hN) (constant_regular _)
theorem product_regular (z B K N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN productF (productData z B K N) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (difference_regular K N hN) (constant_regular _)
theorem exponent_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (product_regular z B (two*R) N (tail_source z R B N h).andE₂.andE₁)
    (GaussianGammaCanonicalTailName.name_regular z R B (two*R) (GaussianGammaCanonicalExponent.tail_source z R B h.andE₁))

theorem difference_sample_bound (p K N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (ap2 differenceF p (differenceData K N)) (one+K) one := by
  have first := bounded_sum_one
    (fixed_sample_bound (addPrecision p) N hN) (bounded_negative _ _ _ (le_refl one) (harmonic_point_bound K))
  exact bound_congr (GaussianNameArithmetic.add_at fixedF constantF N (qnegative (harmonicPoint K)) p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr
      (bound_congr (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (constant_at _ _).eqSymm)
        (.eqRefl _) (.eqRefl _) first))

theorem product_sample_bound (p z R B K N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (ap2 productF p (productData z B K N)) ((one+K)*R) one := by
  let t := GaussianFastValueCut.exponent
    (GaussianNameArithmetic.multiplyModulus differenceF constantF (differenceData K N) (ofGaussian z B)) p
  have first := bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) (difference_sample_bound t K N hN)
    (GaussianGammaEulerHead.fraction_disk z R B h.andE₂.andE₁ h.andE₂.andE₂)
  exact bound_congr (GaussianNameArithmetic.multiply_at differenceF constantF (differenceData K N) (ofGaussian z B) p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr
      (bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (constant_at _ _).eqSymm)
        (.eqRefl _) (by ipra_ring) first))

theorem later_exponent_bound (p s z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N)
    (hps : Γ ⊢[PRAAx] le p s) : Γ ⊢[PRAAx] bounded (ap2 exponentF s (exponentData z R B N))
      (((one+two*R)*R)*(two*unit p)+(R*unit p+one)) (two*unit p) := by
  have hq : Γ ⊢[PRAAx] le p (addPrecision s) := le_trans hps (le_add_right _ _)
  have tail := later_tail_half_bound p (addPrecision s) z R B (two*R)
    (GaussianGammaCanonicalExponent.tail_source z R B h.andE₁) hq
  have sum := bounded_sum _ _ _ _ _ _ (le_refl one)
    (positive_product _ _ (le_succ_self one) (unit_positive p))
    (product_sample_bound (addPrecision s) z R B (two*R) N h.andE₁ (tail_source z R B N h).andE₂.andE₁) tail
  exact bound_congr (GaussianNameArithmetic.add_at productF GaussianGammaCanonicalTailName.pointF
    (productData z B (two*R) N) (GaussianGammaCanonicalTailName.data z R B (two*R)) s).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (positive_product _ _ (le_succ_self one) (unit_positive p))).iffMpr
      (bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) sum))

def combinedF : PR 2 := GaussianNameArithmetic.addF exponentF (negativeF GaussianGammaCanonicalTailName.pointF)
def combinedData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData (exponentData z R B N)
  (negativeData (GaussianGammaCanonicalTailName.data z R B N))
def combinedPoint (p z R B N : PTm n) : PTm n := ap2 combinedF p (combinedData z R B N)
ipra_subst combinedData
ipra_subst combinedPoint

theorem combined_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN combinedF (combinedData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (exponent_regular z R B N h)
    (GaussianNameRingLaws.negative_fast _ _ (GaussianGammaCanonicalTailName.name_regular z R B N (tail_source z R B N h)))

theorem combined_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (combinedPoint p z R B N) (numericalRadius R*unit p+one) (unit p) :=
  combined_point_bound_of_exponent exponentF p (exponentData z R B N) z R B N
    (tail_source z R B N h) (later_exponent_bound p (addPrecision p) z R B N h (le_add_right _ _))

theorem combined_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] rawEnvelope combinedF (combinedData z R B N) (numericalRadius R) one one := by
  apply envelope_of_sample_bound
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [combinedPoint,Syn.shift,subst_combinedData,GaussianGammaCanonicalExponentBound.subst_numericalRadius,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    combined_point_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

def correctedF : PR 2 := GaussianExactDiskShrinking.nameF combinedF
def correctedData (z R B N : PTm n) : PTm n := GaussianExactDiskShrinking.data (combinedData z R B N) (numericalRadius R) one one
ipra_subst correctedData

theorem corrected_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN correctedF (correctedData z R B N) :=
  GaussianExactDiskShrinking.name_regular _ _ _ _ _ (le_refl _) (combined_regular z R B N h) (combined_envelope z R B N h)
theorem corrected_cross (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent correctedF combinedF (correctedData z R B N) (combinedData z R B N) :=
  GaussianExactDiskShrinking.cross_equivalent _ _ _ _ _ (le_refl _) (combined_regular z R B N h) (combined_envelope z R B N h)
theorem corrected_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 correctedF p (correctedData z R B N)) (numericalRadius R) one :=
  GaussianExactDiskShrinking.sample_bound _ p _ _ _ _ (le_refl _) (combined_envelope z R B N h)
theorem corrected_exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input correctedF (numericalRadius R) (correctedData z R B N) :=
  corrected_exponential_input_of_envelope combinedF (combinedData z R B N) (numericalRadius R)
    (combined_regular z R B N h) (combined_envelope z R B N h)

theorem corrected_finite_exponential_bound (p K z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    bounded (GaussianRationalPolynomialExponential.scalarSum (ap2 correctedF p (correctedData z R B N)) K)
      (pw (num 3) (numericalRadius R)) one :=
  GaussianPositiveExponentialMajorant.disk_bound _ _ _ (corrected_point_bound p z R B N h)

theorem original_fixed_euler_sample_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ bounded (ap2 fixedF (var 0) (var 1)) one one) :=
  closeUniv 2 (.impI (fixed_sample_bound _ _ Prf.hyp0))
theorem original_fixed_euler_exponent_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ rawEnvelope combinedF (combinedData (var 0) (var 1) (var 2) (var 3))
      (numericalRadius (var 1)) one one) := closeUniv 4 (.impI (combined_envelope _ _ _ _ Prf.hyp0))
theorem original_fixed_euler_exact_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ pointCN correctedF (correctedData (var 1) (var 2) (var 3) (var 4)) ⋏
      (crossEquivalent correctedF combinedF (correctedData (var 1) (var 2) (var 3) (var 4))
        (combinedData (var 1) (var 2) (var 3) (var 4)) ⋏
       bounded (ap2 correctedF (var 0) (correctedData (var 1) (var 2) (var 3) (var 4))) (numericalRadius (var 2)) one)) :=
  closeUniv 5 (.impI (.andI (corrected_regular _ _ _ _ Prf.hyp0)
    (.andI (corrected_cross _ _ _ _ Prf.hyp0) (corrected_point_bound _ _ _ _ _ Prf.hyp0))))
theorem original_fixed_euler_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ GaussianRadiusExponentialName.input correctedF
      (numericalRadius (var 1)) (correctedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (corrected_exponential_input _ _ _ _ Prf.hyp0))
theorem original_fixed_euler_finite_exponential_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 2) (var 3) (var 4) (var 5) ⟶ bounded
      (GaussianRationalPolynomialExponential.scalarSum (ap2 correctedF (var 0) (correctedData (var 2) (var 3) (var 4) (var 5))) (var 1))
      (pw (num 3) (numericalRadius (var 3))) one) := closeUniv 6 (.impI (corrected_finite_exponential_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFixedEulerExponent
