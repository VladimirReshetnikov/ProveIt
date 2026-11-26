import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationProduct
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaMinimumCenterRate
import IPRADerivations.Analysis.Stirling.GaussianStirlingRationalTelescopers

/-!
# A common rational denominator for the Gamma minimum comparison

The selected dyadic base and a positive rational target are lifted to
one denominator. Original logarithmic integral properness carries the
stationary residual to that encoding, with the independent output
clock allowances and a uniform leading constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumRationalBase

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (lower)
open GaussianGammaDigammaDyadicMesh (grid grid_positive)
open GaussianGammaDigammaLocationInput (lower_bound upper_bound rational_source)
open GaussianGammaDigammaLocationProduct (derivativeBudget native_derivative_residual_at)
open GaussianGammaDigammaNative (derivativeData)
open GaussianGammaMinimumCenterRate (rateCost)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameRingLaws (zeroF zero_at zero_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (arg euler_real_source)
open GaussianStirlingRationalTelescopers (fraction_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF

def baseNumerator (k d : PTm n) : PTm n := d*lower k
def targetNumerator (k c : PTm n) : PTm n := grid k*c
def denominator (k d : PTm n) : PTm n := d*grid k
def residualCost : PTm n := derivativeBudget+one
def minimumCost (M : PTm n) : PTm n := rateCost M residualCost

@[simp] theorem subst_baseNumerator {m : ℕ} (σ : Fin n → PTm m) (k d : PTm n) :
    Syn.subst σ (baseNumerator k d) = baseNumerator (Syn.subst σ k) (Syn.subst σ d) := by
  simp [baseNumerator]
@[simp] theorem subst_targetNumerator {m : ℕ} (σ : Fin n → PTm m) (k c : PTm n) :
    Syn.subst σ (targetNumerator k c) = targetNumerator (Syn.subst σ k) (Syn.subst σ c) := by
  simp [targetNumerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (k d : PTm n) :
    Syn.subst σ (denominator k d) = denominator (Syn.subst σ k) (Syn.subst σ d) := by
  simp [denominator]
@[simp] theorem subst_residualCost {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (residualCost : PTm n) = (residualCost : PTm m) := by
  simp [residualCost,one]
@[simp] theorem subst_minimumCost {m : ℕ} (σ : Fin n → PTm m) (M : PTm n) :
    Syn.subst σ (minimumCost M) = minimumCost (Syn.subst σ M) := by
  simp [minimumCost]

theorem base_source (k d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (baseNumerator k d) (denominator k d) :=
  .andI (positive_product _ _ hd (rational_source k).andE₁) (positive_product _ _ hd (grid_positive k))

theorem chord_domain (k c d M : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (hM : Γ ⊢[PRAAx] le two M) (cap : Γ ⊢[PRAAx] le c (M*d)) :
    Γ ⊢[PRAAx] GaussianGammaMinimumSignedStep.domain (baseNumerator k d) (targetNumerator k c) (denominator k d) M := by
  have low := upper_bound (Γ := Γ) k
  have aBound : Γ ⊢[PRAAx] le (baseNumerator k d) (M*denominator k d) := by
    unfold baseNumerator denominator
    let 𝔞 := fun t : PTm n => Groth.ι (IPRA.Q.mk Γ t)
    ipra_le 𝔞 d*sl low+𝔞 d*𝔞 (grid k)*sl hM
  have cBound : Γ ⊢[PRAAx] le (targetNumerator k c) (M*denominator k d) := by
    unfold targetNumerator denominator
    ipra_le (Groth.ι (IPRA.Q.mk Γ (grid k)))*sl cap
  exact .andI (base_source k d hd) (.andI (positive_product _ _ (grid_positive k) hc) (.andI aBound cBound))

theorem rescaled_fraction (k d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fraction (baseNumerator k d) (denominator k d) ≐ fraction (lower k) (grid k) :=
  fraction_same _ _ _ _ (base_source k d hd).andE₂ (grid_positive k)
    (by unfold baseNumerator denominator; ipra_ring)

theorem target_fraction (k c d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fraction (targetNumerator k c) (denominator k d) ≐ fraction c d :=
  fraction_same _ _ _ _ (base_source k d hd).andE₂ hd
    (by unfold targetNumerator denominator; ipra_ring)

private theorem rescaled_derivative_cross (k d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] crossEquivalent IF IF (derivativeData (baseNumerator k d) (denominator k d))
      (derivativeData (lower k) (grid k)) :=
  GaussianEulerLogarithmicImproperInputProperness.original_improper_proper one _ _ _ _ _ _ _ _
    (.andI (euler_real_source _ _ (base_source k d hd)).andE₁
      (.andI (euler_real_source _ _ (rational_source k)).andE₁ (rescaled_fraction k d hd)))

private theorem residual_diagonal (t k d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 IF t (derivativeData (baseNumerator k d) (denominator k d)))
      (ap2 zeroF t zero) (diagonalNumerator residualCost (unit k) one t) (diagonalDenominator (unit k) t) := by
  let U := unit k
  let V := unit t
  let D := U*V
  have hU := unit_positive (Γ := Γ) k
  have hV := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hU hV
  have near := cross_at IF IF _ _ t k (rescaled_derivative_cross k d hd)
  have first := distance_congr (.eqRefl _) (.eqRefl _) (add_comm V U) (mul_comm V U) near
  have last := distance_radius_mono _ _ _ _ (derivativeBudget*V) D hU hD
    (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) (native_derivative_residual_at k)
  exact distance_congr (.eqRefl _) (zero_at t zero).eqSymm
    (by unfold diagonalNumerator residualCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first last)

theorem rescaled_derivative_residual (k d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    independentRate IF zeroF (derivativeData (baseNumerator k d) (denominator k d)) zero residualCost (unit k) := by
  refine independent_rate IF zeroF _ _ residualCost (unit k) one (unit_positive k)
    (GaussianGammaDigammaNative.derivative_regular _ _ (base_source k d hd)) (zero_fast zero) (.allI ?_)
  have hd' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by
    simpa [Fm.shift,Syn.shift,one] using hd.shift
  simpa [diagonalEnvelope,Syn.shift,one] using residual_diagonal (var 0) (Syn.shift k) (Syn.shift d) hd'

theorem actual_rescaled_dyadic_Gamma_derivative_residual_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶ independentRate IF zeroF
        (derivativeData (baseNumerator (var 0) (var 1)) (denominator (var 0) (var 1))) zero residualCost (unit (var 0))) :=
  closeUniv 2 (.impI (rescaled_derivative_residual _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumRationalBase
