import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaPositiveStationary
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# An explicit admissible increment at the positive Gamma critical point

The selected dyadic location is already admitted to the original
positive Gamma evaluator, and its first Euler derivative is zero.
At each requested precision a positive dyadic increment meets the
original derivative modulus and the apartness test for the quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationGammaDerivative

open_ipra
open ComplexLogarithmRemainder (oneCode normSq normSq_one)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaDigammaLocationInput (named_source)
open GaussianGammaDigammaPositiveStationary (original_difference_quotient_rate)
open GaussianNameRingLaws (zeroF)
open GaussianNamedGammaEulerFirstDerivative (source quotientF quotientData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def modulus (p x : PTm n) : PTm n :=
  GaussianNamedEulerLogarithmicNamedDerivative.incrementModulus locationF p zero x one
def stepAnchor (p x : PTm n) : PTm n := exponent (modulus p x) p
def stepData (p x : PTm n) : PTm n := ofGaussian oneCode (unit (stepAnchor p x))

theorem modulus_positive (p x : PTm n) : Γ ⊢[PRAAx] le one (modulus p x) :=
  GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _

private theorem radius_bound (M D : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hD : Γ ⊢[PRAAx] le one D) (hMD : Γ ⊢[PRAAx] le M D) :
    Γ ⊢[PRAAx] bounded (ofGaussian oneCode D) one M := by
  have h := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hMD hMD
  have e : Γ ⊢[PRAAx] (M*M)*normSq oneCode ≐ M*M :=
    (congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)
  exact bounded_of_cleared _ _ D one M hD hM (ofGaussian_represents _ _ hD)
    (le_congr e.eqSymm (by ipra_ring) h)

private theorem apart_constant (a : PTm n) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input constantF a (ofGaussian oneCode (unit a)) := by
  let D := unit a
  let q := ofGaussian oneCode D
  have hd := unit_positive (Γ := Γ) a
  have e : Γ ⊢[PRAAx] (D*D)*normSq oneCode ≐ D*D :=
    (congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)
  have lower : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q D :=
    GaussianRationalLowerBounds.lower_from_representation q oneCode D one D hd hd
      (ofGaussian_represents _ _ hd)
      (le_congr (by ipra_ring) e.eqSymm (le_refl (D*D)))
  exact .andI (constant_regular q)
    (GaussianNameReciprocal.lower_congr (constant_at (GaussianNameReciprocal.anchor a) q).eqSymm (.eqRefl _) lower)

private theorem constant_small (M D : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hD : Γ ⊢[PRAAx] le one D) (hMD : Γ ⊢[PRAAx] le M D) :
    Γ ⊢[PRAAx] smallSamples constantF (ofGaussian oneCode D) one M := by
  let Δ := Γ.map Fm.shift
  let sh (v : PTm n) := Syn.shift v
  have ma : Δ ⊢[PRAAx] le one (sh M) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hM.shift
  have da : Δ ⊢[PRAAx] le one (sh D) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift
  have md : Δ ⊢[PRAAx] le (sh M) (sh D) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le] using hMD.shift
  refine .allI ?_
  have step := bound_congr (constant_at (var 0) (ofGaussian oneCode (sh D))).eqSymm
    (.eqRefl _) (.eqRefl _) (radius_bound (sh M) (sh D) ma da md)
  simpa only [smallSamples,Syn.shift,sh,GaussianRationalHorner.subst_ofGaussian,
    ComplexLogarithmRemainder.subst_oneCode,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using step

theorem step_source (p x : PTm n) :
    Γ ⊢[PRAAx] source locationF constantF p x (stepData p x) one (stepAnchor p x) := by
  let M := modulus p x
  let a := stepAnchor p x
  let D := unit a
  have hM := modulus_positive (Γ := Γ) p x
  have hD := unit_positive (Γ := Γ) a
  have budget : Γ ⊢[PRAAx] le (M*unit p) D := query_budget M p
  have pays : Γ ⊢[PRAAx] le M D := le_trans
    (le_congr (one_mul M) (mul_comm _ _) (mul_le_mul_right M (unit_positive (Γ := Γ) p))) budget
  exact .andI (named_source x) (.andI (apart_constant a) (constant_small M D hM hD pays))

theorem original_step_quotient_rate (p x : PTm n) :
    Γ ⊢[PRAAx] independentRate (quotientF locationF constantF) zeroF
      (quotientData locationF constantF x (stepData p x) one (stepAnchor p x)) x one (unit p) :=
  original_difference_quotient_rate constantF p x (stepData p x) (stepAnchor p x) (step_source p x)

theorem actual_positive_Gamma_critical_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source locationF constantF (var 0) (var 1) (stepData (var 0) (var 1)) one (stepAnchor (var 0) (var 1)) ⋏
      independentRate (quotientF locationF constantF) zeroF
        (quotientData locationF constantF (var 1) (stepData (var 0) (var 1)) one (stepAnchor (var 0) (var 1)))
        (var 1) one (unit (var 0))) :=
  closeUniv 2 (.andI (step_source _ _) (original_step_quotient_rate _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationGammaDerivative
