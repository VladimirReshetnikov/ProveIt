import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsGrid

/-!
# Explicit upward-stable mesh and precision for the original IBP telescope

The computed mesh pays the genuine relative-step guard and quadratic
mesh error. The original evaluator precision pays the accumulated finite
sampling error. Any larger mesh and precision retain the conclusion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGridBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsGrid (endpoint operatorF numerator denominator)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrandName (fixedData)
open GaussianCompactRiemannName (quadrature)
open GaussianEulerIntegrationByPartsStep (curvature)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observationCost (R E T : PTm n) : PTm n := T*GaussianEulerIntegrationByPartsProductStep.observationCost R E T
def minimumMesh (j R E T C : PTm n) : PTm n := one+(R+one)*C+curvature R E T*C*C*unit (succ j)
def minimumPrecision (j R E T N : PTm n) : PTm n := GaussianFastValueCut.exponent (observationCost R E T*N) (succ j)

theorem source_of_mesh (j z R B a C E T N : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hC : Γ ⊢[PRAAx] le one C) (hm : Γ ⊢[PRAAx] le (minimumMesh j R E T C) N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsGrid.source z R B a C E T N := by
  have hn : Γ ⊢[PRAAx] le one N := le_trans (le_trans (le_add_right one ((R+one)*C)) (le_add_right _ _)) hm
  have leading : Γ ⊢[PRAAx] le ((R+one)*C) N := le_trans
    (le_trans (le_add_left ((R+one)*C) one) (le_add_right _ _)) hm
  have aN : Γ ⊢[PRAAx] le N (a*N) := le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N h.andE₂.andE₁)
  have cN : Γ ⊢[PRAAx] le C N := le_trans (le_congr (one_mul C) (.eqRefl _)
    (mul_le_mul_right C (le_add_left one R))) leading
  have nEN : Γ ⊢[PRAAx] le N (E*N) := le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N h.andE₁.andE₂.andE₁)
  exact .andI h (.andI hn (.andI hC (.andI (le_trans leading aN) (le_trans cN nEN))))

theorem numerical_budget (j p R E T C N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hm : Γ ⊢[PRAAx] le (minimumMesh j R E T C) N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision j R E T N) p) : Γ ⊢[PRAAx]
    le (numerator p R E T C N*unit j) (denominator p E N) := by
  let S := unit (succ j)
  let K := curvature R E T
  let Z := observationCost R E T
  let P := unit p
  have hm' : Γ ⊢[PRAAx] le (K*C*C*S) N := le_trans (le_add_left _ _) hm
  have hp' : Γ ⊢[PRAAx] le (Z*N*S) P := le_trans (GaussianFastValueCut.query_budget (Z*N) (succ j))
    (GaussianExponentialReference.unit_monotone hp)
  have first : Γ ⊢[PRAAx] le (K*C*C*S*P) (E*E*N*P) := le_trans (mul_le_mul_right P hm')
    (le_congr (one_mul (N*P)) (by ipra_ring) (mul_le_mul_right (N*P) (positive_product E E hE hE)))
  have second := mul_le_mul_right (E*E*N) hp'
  have total := add_le_add₂ first second
  have twice : Γ ⊢[PRAAx] le (two*(numerator p R E T C N*unit j)) (two*denominator p E N) := by
    have growth := natEq (pw_succ (Γ := Γ) two j)
    apply le_congr _ _ total
    · apply deriveNat
      dsimp only [S,K,Z,P,numerator,observationCost,unit]
      ipra_simps
      rw [growth]
      ring
    · dsimp only [denominator,P]
      ipra_ring
  exact RationalValueBounds.positive_cancel (le_succ_self one) twice

/-- Source-only finite telescope at any mesh and actual original
evaluation precision above the computed thresholds. -/
theorem original_dyadic_error (j p z R B a C E T N : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hC : Γ ⊢[PRAAx] le one C)
    (hm : Γ ⊢[PRAAx] le (minimumMesh j R E T C) N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision j R E T N) p) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalMetric.qsub (endpoint N p z B a C E N) (endpoint zero p z B a C E N))
      (quadrature operatorF p N a C E (fixedData z B)) one (unit j) := by
  have source := source_of_mesh j z R B a C E T N h hC hm
  have hE := h.andE₁.andE₂.andE₁
  have hn := source.andE₂.andE₁
  have old : Γ ⊢[PRAAx] le one (denominator p E N) :=
    positive_product _ _ (positive_product _ _ (positive_product E E hE hE) hn) (unit_positive p)
  exact distance_radius_mono _ _ _ _ one (unit j) old (unit_positive j)
    (le_congr (.eqRefl _) (by dsimp only [denominator]; ipra_ring) (numerical_budget j p R E T C N hE hm hp))
    (GaussianEulerIntegrationByPartsGrid.original_finite_error p z R B a C E T N source)

theorem actual_original_Euler_IBP_computed_dyadic_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      (le one (var 6) ⋏ (le (minimumMesh (var 0) (var 3) (var 7) (var 8) (var 6)) (var 9) ⋏
        le (minimumPrecision (var 0) (var 3) (var 7) (var 8) (var 9)) (var 1)))) ⟶
      distanceBounded (GaussianRationalMetric.qsub (endpoint (var 9) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 9))
        (endpoint zero (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 9)))
        (quadrature operatorF (var 1) (var 9) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4))) one (unit (var 0))) :=
  closeUniv 10 (.impI (original_dyadic_error _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsGridBudget
