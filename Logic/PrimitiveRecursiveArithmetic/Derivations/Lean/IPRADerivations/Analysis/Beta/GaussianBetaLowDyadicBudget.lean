import IPRADerivations.Analysis.Beta.GaussianBetaLowGridError
import IPRADerivations.Analysis.Beta.GaussianBetaSharpPartition

/-!
# Dyadic budgets for the unchanged beta/Euler grid below time one

Any positive common count is allowed. The two original evaluator queries
remain independent and may be any later queries than the computed common
minimum. The exact leading coefficient is one divided by the beta degree,
including zero width. The final wrapper uses the original sharp low width
and denominator without changing the grid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaLowDyadicBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def minimumPrecision (j : PTm n) : PTm n := succ j
def numerator (j N : PTm n) : PTm n := unit j+N
def denominator (j N : PTm n) : PTm n := N*unit j
def source (z R B A a C E N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (le one a ⋏ (le one E ⋏ (le two N ⋏ le (a+C) E)))

theorem query_budget (j p : PTm n) (h : Γ ⊢[PRAAx] le (minimumPrecision j) p) : Γ ⊢[PRAAx]
    le (two*unit j) (unit p) :=
  le_congr ((pw_succ two j).eqTrans (mul_comm _ _)) (.eqRefl _)
    (GaussianExponentialReference.unit_monotone h)

theorem two_query_budget (J P V : PTm n)
    (hp : Γ ⊢[PRAAx] le (two*J) P) (hv : Γ ⊢[PRAAx] le (two*J) V) : Γ ⊢[PRAAx]
    le (J*(P+V)) (P*V) :=
  RationalValueBounds.positive_cancel (le_succ_self one)
    (le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right V hp) (mul_le_mul_right P hv)))

/-- Both original queries are arbitrary later observations. The actual
common mesh is unrestricted beyond positivity. -/
theorem original_low_dyadic_bound (p v j M a C E z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E N)
    (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision j) p)
    (hv : Γ ⊢[PRAAx] le (minimumPrecision j) v) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M a C E (GaussianEulerIntegrandName.fixedData z B))
      (numerator j N) (denominator j N) := by
  have hn := le_trans (le_succ_self one) h.andE₂.andE₂.andE₂.andE₁
  have old := GaussianBetaLowGridError.original_low_grid_unit_error p v M a C E z R B A N
    hM h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂
  have budget := two_query_budget (unit j) (unit p) (unit v) (query_budget j p hp) (query_budget j v hv)
  have compare : Γ ⊢[PRAAx]
      le ((unit p*unit v+N*(unit p+unit v))*denominator j N)
        (numerator j N*(N*unit p*unit v)) :=
    le_congr (by dsimp only [denominator]; ipra_ring) (by dsimp only [numerator]; ipra_ring)
      (add_le_add_right (unit p*unit v*N*unit j) (mul_le_mul_right (N*N) budget))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hn (unit_positive p)) (unit_positive v))
    (positive_product _ _ hn (unit_positive j)) compare old

/-- The exact original interval [1/eta,1] and its original low width;
the beta degree is any fixed numerical N>=2. -/
theorem original_sharp_low_dyadic_bound (p v j M k z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le two N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision j) p)
    (hv : Γ ⊢[PRAAx] le (minimumPrecision j) v) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M one (GaussianBetaSharpPartition.lowWidth k A R)
        (GaussianGammaIntegralCutoffs.etaDen k A R) (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M one (GaussianBetaSharpPartition.lowWidth k A R)
        (GaussianGammaIntegralCutoffs.etaDen k A R) (GaussianEulerIntegrandName.fixedData z B))
      (numerator j N) (denominator j N) := by
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have right : Γ ⊢[PRAAx] le (one+GaussianBetaSharpPartition.lowWidth k A R) (GaussianGammaIntegralCutoffs.etaDen k A R) :=
    le_congr (eq_add_of_le he) (.eqRefl _) (le_refl _)
  exact original_low_dyadic_bound p v j M one (GaussianBetaSharpPartition.lowWidth k A R)
    (GaussianGammaIntegralCutoffs.etaDen k A R) z R B A N
    (.andI h (.andI (le_refl one) (.andI he (.andI hN right)))) hM hp hv

theorem actual_original_low_grid_exact_degree_dyadic_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      ((source (var 7) (var 8) (var 9) (var 10) (var 4) (var 5) (var 6) (var 11) ⋏
        (le one (var 3) ⋏ (le (minimumPrecision (var 2)) (var 0) ⋏ le (minimumPrecision (var 2)) (var 1)))) ⟶
        distanceBounded
          (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 3) (var 4) (var 5) (var 6)
            (GaussianBetaKernelGridComparison.sampleDataBeta (var 7) (var 9) (var 11)))
          (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 3) (var 4) (var 5) (var 6)
            (GaussianEulerIntegrandName.fixedData (var 7) (var 9)))
          (numerator (var 2) (var 11)) (denominator (var 2) (var 11))) :=
  closeUniv 12 (.impI (original_low_dyadic_bound _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem original_eta_to_one_arbitrary_fixed_degree_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((GaussianEulerLowerPowerCoefficients.source (var 5) (var 6) (var 7) (var 8) ⋏
        (le one (var 3) ⋏ (le two (var 9) ⋏
          (le (minimumPrecision (var 2)) (var 0) ⋏ le (minimumPrecision (var 2)) (var 1))))) ⟶
        distanceBounded
          (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 3) one
            (GaussianBetaSharpPartition.lowWidth (var 4) (var 8) (var 6))
            (GaussianGammaIntegralCutoffs.etaDen (var 4) (var 8) (var 6))
            (GaussianBetaKernelGridComparison.sampleDataBeta (var 5) (var 7) (var 9)))
          (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 3) one
            (GaussianBetaSharpPartition.lowWidth (var 4) (var 8) (var 6))
            (GaussianGammaIntegralCutoffs.etaDen (var 4) (var 8) (var 6))
            (GaussianEulerIntegrandName.fixedData (var 5) (var 7)))
          (numerator (var 2) (var 9)) (denominator (var 2) (var 9))) :=
  closeUniv 10 (.impI (original_sharp_low_dyadic_bound _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaLowDyadicBudget
