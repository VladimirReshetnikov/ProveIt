import IPRADerivations.Analysis.Beta.EulerProducts.GaussianBetaFiniteEulerComparison
import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveUniformLowerEndpoint

/-!
# Original finite beta quadrature at a degree-independent cutoff

Choose the left cutoff independently of the beta degree. The
uniform (3A) bound controls the actual lower primitive endpoint
on its unchanged affine-grid clock. The previously checked finite
telescope and finite Euler reciprocal comparison apply verbatim.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaFiniteEulerAtCutoff

open_ipra
open GaussianBetaFiniteEulerComparison (source slack supportWidth supportCells gridPrecision)
open GaussianBetaPrimitiveGridUnscale (quadrature scaledEndpoint demand)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def minimumCutoff (t A : PTm n) : PTm n := GaussianBetaPrimitiveUniformLowerEndpoint.precision (slack t) A
def minimumCells (t k z R B A N : PTm n) : PTm n := supportCells t z R B (etaDen k A R) N
def upperPrecision (t k z R B A N M : PTm n) : PTm n :=
  GaussianBetaUpperGridEndpoint.precision (slack t) z B (etaDen k A R*M) N
def minimumPrecision (t k z R B A N M : PTm n) : PTm n :=
  gridPrecision t z B N M+k+upperPrecision t k z R B A N M
def observation (p k z R B A N M : PTm n) : PTm n :=
  quadrature p z B one (supportWidth (etaDen k A R) N) (etaDen k A R) M N

private theorem evaluation_budgets (t k z R B A N M : PTm n) :
    Γ ⊢[PRAAx] le (gridPrecision t z B N M) (minimumPrecision t k z R B A N M) ⋏
      le k (minimumPrecision t k z R B A N M) ⋏
      le (upperPrecision t k z R B A N M) (minimumPrecision t k z R B A N M) := by
  let g := gridPrecision t z B N M
  let u := upperPrecision t k z R B A N M
  have hGrid : Γ ⊢[PRAAx] le g ((g+k)+u) := le_trans (le_add_right _ _) (le_add_right _ _)
  have hCut : Γ ⊢[PRAAx] le k ((g+k)+u) := le_trans (le_add_left _ _) (le_add_right _ _)
  have hUpper : Γ ⊢[PRAAx] le u ((g+k)+u) := le_add_left _ _
  exact .andI hGrid (.andI hCut hUpper)

theorem original_at_cutoff (t p q k z R B A N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) (hk : Γ ⊢[PRAAx] le (minimumCutoff t A) k)
    (hm : Γ ⊢[PRAAx] le (minimumCells t k z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t k z R B A N M) p) :
    Γ ⊢[PRAAx] distanceBounded (observation p k z R B A N M)
      (ap2 eulerF q (eulerData z R B A N)) (unit t+unit q) (unit t*unit q) := by
  let E := etaDen k A R
  let C := supportWidth E N
  have hN := GaussianBetaFiniteEulerComparison.degree_positive z R B A N h
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand (slack t) N) z R B C E N N) hm
  have budgets := evaluation_budgets (Γ := Γ) t k z R B A N M
  have kp : Γ ⊢[PRAAx] le k p := le_trans budgets.andE₂.andE₁ hp
  have small := GaussianBetaPrimitiveUniformLowerEndpoint.constructive_endpoint_small_at (slack t) k p z R B A N M
    h.andE₁ hN hM hk (le_trans hk kp)
  have lower : Γ ⊢[PRAAx] bounded (scaledEndpoint zero p z B one C E M N) one (unit (slack t)) :=
    GaussianRationalReciprocal.bound_congr (GaussianBetaFiniteEulerComparison.cutoff_lower_endpoint_code k p z R B A N M).eqSymm
      (.eqRefl _) (.eqRefl _) small
  exact GaussianBetaFiniteEulerComparison.full_support_euler_error t p q z R B A E N M h
    (eta_den_positive _ _ _) hm (le_trans budgets.andE₁ hp) (le_trans budgets.andE₂.andE₂ hp) lower

theorem original_degree_independent_cutoff_finite_Euler_inverse_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((source (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
        le (minimumCutoff (var 0) (var 7)) (var 3) ⋏
        le (minimumCells (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 9) ⋏
        le (minimumPrecision (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) (var 1)) ⟶
        distanceBounded (observation (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (ap2 eulerF (var 2) (eulerData (var 4) (var 5) (var 6) (var 7) (var 8)))
          (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 10 (.impI (original_at_cutoff _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaFiniteEulerAtCutoff
