import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaNegativeIntervalInverseRecurrence
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalInverseBound
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalLocation
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationProduct

/-!
# Uniform bounds for the original negative Gamma observations

The positive terminal argument stays in the compact interval [1,2].
A fixed rational separation from the two neighboring poles bounds the
original inverse recurrence multiplier uniformly over input encodings.
These bounds control the genuine Gamma observations at every query.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalUniformBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegralUpperTransfer (paperConstant)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaDigammaLocationProduct (gammaCap)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalGrid (denominator leftIndex room selected)
open GaussianGammaNegativeCriticalLocation (lower)
open GaussianGammaNegativeIntervalInverseBound (bound_from_margin)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse liftedF liftedData original_inverse_product)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiply_at multiplyModulus multiplyRaw)
open GaussianNameEquivalence (cross_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianStirlingGammaLogarithm (arg gammaData gamma_source)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def marginCap (K : PTm n) : PTm n := (K*K)*gammaCap+two
def cap (N : PTm n) : PTm n := marginCap (mesh N)

@[simp] theorem subst_cap {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (cap N) = cap (Syn.subst σ N) := by
  simp [cap,marginCap,gammaCap,two,one]

private theorem positive_compact_source (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (arg (b+a)) two b one := by
  let A := b+a
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hA : Γ ⊢[PRAAx] le A (two*b) := by unfold A; ipra_le sl (le_of_lt h.andE₂)
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (arg A) (two*b) :=
    le_congr (GaussianGammaGaussReference.scaled_one_norm A).eqSymm (.eqRefl _) (le_mul_mono hA hA)
  have edge : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (arg A) one b := by
    unfold GaussianEulerLowerPowerCoefficients.realLower
    apply zle_of_toZ a
    simp only [A,arg,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  exact .andI (.andI (le_refl one) (.andI (.andI hb disk) edge)) (le_succ_self one)

theorem positive_bound (a b q : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    bounded (ap2 gammaF q (gammaData (b+a) b)) gammaCap one := by
  let A := b+a
  let U := unit q
  let C := paperConstant (one : PTm n) two
  have hu := unit_positive (Γ := Γ) q
  have source := positive_compact_source a b h
  have native := gamma_source A b (GaussianGammaNegativeCriticalEndpoints.shifted_source a b h)
  have compact := GaussianGammaHalfPlaneInputContinuity.reciprocal_source (arg A) two b one source
  have same := GaussianGammaRadiusOverlap.original_Gamma_observation_overlap q q (arg A) A two b one b one one native compact
  have localBound := GaussianEulerIntegralUpperBound.original_gamma_bound q (arg A) two b one source
  have both := norm_from_distance _ _ _ _ _ _ (positive_product _ _ hu hu) hu same localBound
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hu hu) hu) (le_refl one) _ both
  change Γ ⊢[PRAAx] le (((U+U)*U+(C*U+one)*(U*U))*one) ((C+num 3)*(U*U*U))
  ipra_le 3*𝔞(U)^2*sl hu

theorem original_gamma_bounded (a b K q N : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hleft : Γ ⊢[PRAAx] le b (K*a)) (hright : Γ ⊢[PRAAx] le b (K*monus b a)) : Γ ⊢[PRAAx]
    bounded (ap2 gammaF q (GaussianGammaNegativeIntervalNative.data a b N)) (marginCap K) one := by
  let c := inverse a b N
  let y := gammaData (b+a) b
  let t := GaussianFastValueCut.exponent (multiplyModulus constantF gammaF c y) q
  let M := (K*K)*gammaCap
  let U := unit q
  have hu := unit_positive (Γ := Γ) q
  have hc : Γ ⊢[PRAAx] bounded c (K*K) one :=
    bound_from_margin a b N (K*K) h (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hleft hright))
  have hct := bound_congr (constant_at t c).eqSymm (.eqRefl _) (.eqRefl _) hc
  have hy := positive_bound a b t h
  have product : Γ ⊢[PRAAx] bounded (multiplyRaw constantF gammaF t c y) M one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hct hy)
  have recoded := (GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr product
  have boundedProduct : Γ ⊢[PRAAx] bounded (ap2 liftedF q (liftedData a b N)) M one :=
    bound_congr (multiply_at constantF gammaF c y q).eqSymm (.eqRefl _) (.eqRefl _) recoded
  have hU := positive_product _ _ hu hu
  have same := cross_at _ _ _ _ q q (original_inverse_product a b N h)
  have both := norm_from_distance _ _ _ _ _ _ hU (le_refl one) same boundedProduct
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU (le_refl one)) (le_refl one) _ both
  change Γ ⊢[PRAAx] le (((U+U)*one+M*(U*U))*one) ((M+two)*((U*U)*one))
  ipra_le 2*𝔞(U)*sl hu

theorem grid_bounded (k q N : PTm n) : Γ ⊢[PRAAx]
    bounded (ap2 gammaF q (GaussianGammaNegativeIntervalNative.data (lower k N) (denominator k N) N)) (cap N) one := by
  let a := lower k N
  let b := denominator k N
  let K := mesh N
  have hi := le_of_lt (selected (Γ := Γ) k N).andE₁
  have h : Γ ⊢[PRAAx] guard a b := GaussianGammaNegativeCriticalGrid.grid_guard k N (leftIndex k N) hi
  have edge : Γ ⊢[PRAAx] le (a+unit k) b := room k N (leftIndex k N) hi
  have eq := natEq (eq_add_of_le (le_of_lt h.andE₂))
  have gap : Γ ⊢[PRAAx] le (unit k) (monus b a) := by ipra_le sl edge with -eq
  refine original_gamma_bounded a b K q N h ?_ ?_
  · unfold b K a denominator lower GaussianGammaNegativeCriticalGrid.numerator
    ipra_le 𝔞(mesh N)*𝔞(leftIndex k N)
  · exact le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right K gap)

theorem actual_original_negative_Gamma_grid_bounded_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (bounded (ap2 gammaF (var 1) (GaussianGammaNegativeIntervalNative.data
        (lower (var 0) (var 2)) (denominator (var 0) (var 2)) (var 2))) (cap (var 2)) one) :=
  closeUniv 3 (grid_bounded _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalUniformBounds
