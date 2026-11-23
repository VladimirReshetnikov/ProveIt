import IPRADerivations.Analysis.GaussianMonomialDecayQuadrature

/-!
# Computed finite mesh budgets for the exact factorial monomial integral

The three original finite errors each spend one quarter of the desired
dyadic allowance. The mesh, evaluation and independent reference clocks
are explicit numerical terms; the leading constant remains 2^(d+1)d!.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMonomialDecayBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianMonomialDecayQuadrature (evaluatorF cap errorNumerator errorDenominator)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget)
open GaussianCompactRiemannName (quadrature)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def meshCost (C d : PTm n) : PTm n := num 3*majorant d*C*C
def precisionCost (C d : PTm n) : PTm n := (majorant d+budget d)*C
def referenceCost (d : PTm n) : PTm n := num 20*majorant d
def minimumMesh (t C d : PTm n) : PTm n := one+C+num 4*meshCost C d*unit t
def minimumPrecision (t C d : PTm n) : PTm n := GaussianFastValueCut.exponent (num 4*precisionCost C d) t
def minimumReference (t d : PTm n) : PTm n := GaussianFastValueCut.exponent (num 4*referenceCost d) t

theorem scalar_budget (p q t N C E d : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hMesh : Γ ⊢[PRAAx] le (num 4*meshCost C d*unit t) N)
    (hPrecision : Γ ⊢[PRAAx] le (num 4*precisionCost C d*unit t) (unit p))
    (hReference : Γ ⊢[PRAAx] le (num 4*referenceCost d*unit t) (unit q)) : Γ ⊢[PRAAx]
    le (errorNumerator p q N C E d*unit t) (errorDenominator p q N E) := by
  let P := unit p
  let Q := unit q
  let U := unit t
  let D := errorDenominator p q N E
  let X := num 3*majorant d*C*C*P*Q
  let Y := two*E*N*C*(majorant d+budget d)*Q
  let Z := num 40*majorant d*E*E*N*P
  have factor : Γ ⊢[PRAAx] le one (two*E*E) := positive_product _ _ (positive_product _ _ (le_succ_self one) hE) hE
  have firstBase : Γ ⊢[PRAAx] le (N*(P*Q)) D :=
    le_congr (by ipra_ring) (by dsimp only [D,errorDenominator,GaussianEulerHalfDecayLeftNorm.errorDenominator]; ipra_ring)
      (mul_le_mul_right (N*P*Q) factor)
  have first : Γ ⊢[PRAAx] le (num 4*X*U) D :=
    le_trans (le_congr (by dsimp only [X,U,P,Q,meshCost]; ipra_ring) (.eqRefl _)
      (mul_le_mul_right (P*Q) hMesh)) firstBase
  have secondBase : Γ ⊢[PRAAx] le ((two*E*N*Q)*P) D :=
    le_congr (by ipra_ring) (by dsimp only [D,errorDenominator,GaussianEulerHalfDecayLeftNorm.errorDenominator]; ipra_ring)
      (mul_le_mul_right (two*E*N*P*Q) hE)
  have second : Γ ⊢[PRAAx] le (num 4*Y*U) D :=
    le_trans (le_congr (by dsimp only [Y,U,precisionCost]; ipra_ring) (mul_comm _ _)
      (mul_le_mul_right (two*E*N*Q) hPrecision)) secondBase
  have third : Γ ⊢[PRAAx] le (num 4*Z*U) D :=
    le_congr (by dsimp only [Z,U,referenceCost]; ipra_ring)
      (by dsimp only [D,errorDenominator,GaussianEulerHalfDecayLeftNorm.errorDenominator]; ipra_ring)
      (mul_le_mul_right (two*E*E*N*P) hReference)
  have sum : Γ ⊢[PRAAx] le (num 4*(errorNumerator p q N C E d*U)) ((num 3)*D) :=
    le_congr (by dsimp only [X,Y,Z,P,Q,errorNumerator]; ipra_ring) (by ipra_ring) (add_le_add₂ (add_le_add₂ first second) third)
  exact RationalValueBounds.positive_cancel (le_of_eq_add (d := num 3) (by ipra_ring))
    (le_trans sum (le_of_eq_add (d := D) (by ipra_ring)))

theorem mesh_threshold (t N C d : PTm n) (h : Γ ⊢[PRAAx] le (minimumMesh t C d) N) : Γ ⊢[PRAAx]
    le one N ⋏ le C N ⋏ le (num 4*meshCost C d*unit t) N := by
  have a : Γ ⊢[PRAAx] le one (minimumMesh t C d) := le_of_eq_add (d := C+num 4*meshCost C d*unit t) (by unfold minimumMesh; ipra_ring)
  have b : Γ ⊢[PRAAx] le C (minimumMesh t C d) := le_of_eq_add (d := one+num 4*meshCost C d*unit t) (by unfold minimumMesh; ipra_ring)
  have c : Γ ⊢[PRAAx] le (num 4*meshCost C d*unit t) (minimumMesh t C d) := le_of_eq_add (d := one+C) (by unfold minimumMesh; ipra_ring)
  exact .andI (le_trans a h) (.andI (le_trans b h) (le_trans c h))

/-- Actual finite monomial quadrature from time one, at every finer
mesh and either independently finer original observation precision. -/
theorem original_grid_dyadic_bound (p q t N C E d : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le one C)
    (hN : Γ ⊢[PRAAx] le (minimumMesh t C d) N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t C d) p)
    (hq : Γ ⊢[PRAAx] le (minimumReference t d) q) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N E C E d) (cap d*unit t+one) (unit t) := by
  have mesh := mesh_threshold t N C d hN
  have step : Γ ⊢[PRAAx] le C ((two*E)*N) := le_trans mesh.andE₂.andE₁
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (positive_product _ _ (le_succ_self one) hE)))
  have prec : Γ ⊢[PRAAx] le (num 4*precisionCost C d*unit t) (unit p) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hp)
  have ref : Γ ⊢[PRAAx] le (num 4*referenceCost d*unit t) (unit q) :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hq)
  have native := scalar_budget p q t N C E d hE mesh.andE₂.andE₂ prec ref
  have compare : Γ ⊢[PRAAx]
      le ((cap d*errorDenominator p q N E+errorNumerator p q N C E d)*unit t)
        ((cap d*unit t+one)*errorDenominator p q N E) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (cap d*errorDenominator p q N E*unit t) native)
  exact bounded_radius_mono _ _ _ _ _
    (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q N E mesh.andE₁ hE) (unit_positive t) compare
    (GaussianMonomialDecayQuadrature.original_grid_uniform_bound p q N C E d mesh.andE₁ hC hE step)

theorem original_finitely_refined_monomial_factorial_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 5) ⋏ le one (var 4) ⋏ le (minimumMesh (var 2) (var 4) (var 6)) (var 3) ⋏
      le (minimumPrecision (var 2) (var 4) (var 6)) (var 0) ⋏ le (minimumReference (var 2) (var 6)) (var 1)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 3) (var 5) (var 4) (var 5) (var 6))
        (cap (var 6)*unit (var 2)+one) (unit (var 2))) :=
  closeUniv 7 (.impI (original_grid_dyadic_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianMonomialDecayBudget
