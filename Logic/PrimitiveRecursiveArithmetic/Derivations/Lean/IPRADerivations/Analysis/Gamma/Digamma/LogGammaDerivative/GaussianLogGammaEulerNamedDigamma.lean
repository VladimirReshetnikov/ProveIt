import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerDigammaContinuity
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift

/-!
# The literal C27 digamma on regular complex right-half-plane names

The generic half-plane lift uses the actual signed-rational observation
and evaluates the checked cofinal partial-fraction program. The common
real margin `1/K` gives the evaluator gain `K²+2`. The clock does not
need a separate upper radius for the Lipschitz constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 470000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerSlopeContinuity (input coefficient)
open GaussianLogGammaEulerDigammaContinuity (canonical_fraction_lipschitz)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate point realNumerator imagNumerator denominator sign
  subst_realNumerator subst_imagNumerator subst_denominator subst_sign)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianLogGammaEulerHead (subst_rowData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "digammaF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "digammaData" => GaussianLogGammaEulerDigammaFractionsCofinal.data

def pointData (q : PTm n) : PTm n := digammaData (realNumerator q) (imagNumerator q) (denominator q) (sign q)
def rationalData : PR 1 := PTm.toPR (pointData (var 0) : PTm 1)
def gain : PR 2 := PTm.toPR (coefficient (var 1) : PTm 2)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (pointData q) = pointData (Syn.subst σ q) := by
  simp only [pointData, subst_rowData, subst_realNumerator, subst_imagNumerator, subst_denominator, subst_sign]

theorem rational_data_at (q : PTm n) : Γ ⊢[PRAAx] ap1 rationalData q ≐ pointData q := by
  simpa only [rationalData, ap1, subst_pointData, Syn.subst_var, Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (pointData (var 0) : PTm 1) ![q]

theorem gain_at (R K : PTm n) : Γ ⊢[PRAAx] ap2 gain R K ≐ coefficient K := by
  simpa only [gain, ap2, coefficient, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, two, one, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using
    toPR_eq (Γ := Γ) (coefficient (var 1) : PTm 2) ![R, K]

theorem variation (x y R K H E : PTm n) (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hE : Γ ⊢[PRAAx] le one E) (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) H E) :
    Γ ⊢[PRAAx] independentRate digammaF digammaF (ap1 rationalData x) (ap1 rationalData y) (ap2 gain R K * H) E := by
  have hK := GaussianDominantScalarOrder.factor_positive_left K (realNumerator x)
    (le_trans hx.andE₁.andE₁.andE₂ hx.andE₂.andE₁)
  have cert : Γ ⊢[PRAAx] input (realNumerator x) (denominator x) (sign x) (realNumerator y) (denominator y) (sign y) K :=
    .andI hx.andE₁.andE₁ (.andI hy.andE₁.andE₁ (.andI hK (.andI hx.andE₂.andE₁ hy.andE₂.andE₁)))
  have rate : Γ ⊢[PRAAx] independentRate digammaF digammaF (pointData x) (pointData y) (coefficient K * H) E :=
    canonical_fraction_lipschitz (realNumerator x) (imagNumerator x) (denominator x) (sign x)
      (realNumerator y) (imagNumerator y) (denominator y) (sign y) K H E cert hE near
  let formula : Fm PTm 4 := independentRate digammaF digammaF (var 0) (var 1) (var 2) (var 3)
  have replace := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) formula
    ![pointData x, pointData y, coefficient K * H, E]
    ![ap1 rationalData x, ap1 rationalData y, ap2 gain R K * H, E]
    (fun i => by
      fin_cases i
      · exact (rational_data_at x).eqSymm
      · exact (rational_data_at y).eqSymm
      · exact congrMul (gain_at R K).eqSymm (.eqRefl H)
      · exact .eqRefl E)
    (by simpa only [formula, subst_independentRate, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using rate)
  simpa only [formula, subst_independentRate, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using replace

def rationalMap : GaussianNamedRightHalfPlaneLift.RationalMap where
  evaluator := digammaF
  rationalData := rationalData
  gain := gain
  variation := fun x y R K H E hx hy hE _ near => variation x y R K H E hx hy hE near

abbrev source (f : PR 2) (x M R : PTm n) : Fm PTm n := GaussianNamedRightHalfPlaneLift.source f x M R
abbrev nameF (f : PR 2) : PR 2 := GaussianNamedRightHalfPlaneLift.nameF rationalMap f
abbrev data (x M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.data x M R

theorem sample_at (f : PR 2) (p x M R : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p (data x M R) ≐
    GaussianNamedRightHalfPlaneLift.sample rationalMap f p x M R :=
  GaussianNamedRightHalfPlaneLift.sample_at rationalMap f p x M R

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) : Γ ⊢[PRAAx] pointCN (nameF f) (data x M R) :=
  GaussianNamedRightHalfPlaneLift.name_regular rationalMap f x M R h

theorem proper (f g : PR 2) (x y M R : PTm n) (hx : Γ ⊢[PRAAx] source f x M R) (hy : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y M R) :=
  GaussianNamedRightHalfPlaneLift.proper rationalMap f g x y M R hx hy he

theorem actual_named_complex_digamma_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigamma
