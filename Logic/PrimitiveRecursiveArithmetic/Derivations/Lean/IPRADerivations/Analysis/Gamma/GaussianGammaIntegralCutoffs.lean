import IPRADerivations.Analysis.Polynomials.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.Exponential.GaussianExponentialReference
import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Numerical cutoffs for the Euler integral

This checks the packet's exact arithmetic for the two improper
endpoints and the compact mesh. The left endpoint is the rational
`1/etaDen`; it has the exact dyadic A-th-root denominator. The right
endpoint is `top = 2L`. Once the two tail estimates are available,
their common dyadic denominator spends the stated error budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaIntegralCutoffs

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalHorner (positive_product)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def tailCoefficient (R : PTm n) : PTm n := unit (succ R)*fact R
def height (p A R : PTm n) : PTm n := p+A+tailCoefficient R+num 10
def etaDen (p A R : PTm n) : PTm n := unit (A*height p A R)
def top (p A R : PTm n) : PTm n := two*height p A R
def lipschitz (p A R : PTm n) : PTm n :=
  (etaDen p A R+pw (top p A R) R)*(succ R*etaDen p A R+one)
def meshCost (p A R : PTm n) : PTm n := lipschitz p A R*top p A R*top p A R
def cells (p A R : PTm n) : PTm n := unit (p+num 6)*(one+meshCost p A R)

theorem height_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (height p A R) := by
  unfold height
  ipra_le 𝔞 p+𝔞 A+𝔞(tailCoefficient R)+9

theorem eta_den_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (etaDen p A R) :=
  unit_positive _

theorem top_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (top p A R) :=
  positive_product _ _ (zero_lt_succ one) (height_positive p A R)

theorem exact_eta_root_power (p A R : PTm n) :
    Γ ⊢[PRAAx] pw (unit (height p A R)) A ≐ etaDen p A R := by
  unfold etaDen unit
  exact (pw_mul _ _ _).eqTrans (congrAp2 powF (mul_comm _ _) (.eqRefl _))

private theorem unit_grows (t : PTm n) : Γ ⊢[PRAAx] lt (unit t) (unit (succ t)) := by
  have e := natEq (pw_succ (Γ := Γ) two t)
  have h := unit_positive (Γ := Γ) t
  change Γ ⊢[PRAAx] le one (pw two t) at h
  unfold lt unit
  ipra_le sl h using
    rw [e]
    ring

theorem omitted_tail_budget (p A R : PTm n) :
    Γ ⊢[PRAAx] lt ((A+tailCoefficient R)*unit (p+num 6)) (unit (height p A R)) := by
  let S := A+tailCoefficient R
  let t := p+num 6+S
  have b : Γ ⊢[PRAAx] le (S*unit (p+num 6)) (unit t) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two (p+num 6) S).eqSymm)
      (mul_le_mul_right (unit (p+num 6)) (LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.le_pow_self S))
  have later : Γ ⊢[PRAAx] le (succ t) (height p A R) := by
    unfold t S height
    ipra_le 3
  exact lt_of_le_of_lt b (lt_of_lt_of_le (unit_grows t) (unit_monotone later))

theorem mesh_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (cells p A R) :=
  positive_product _ _ (unit_positive _) (le_add_right _ _)

theorem mesh_error_budget (p A R : PTm n) :
    Γ ⊢[PRAAx] lt (meshCost p A R*unit (p+num 6)) (cells p A R) := by
  have hp := unit_positive (Γ := Γ) (p+num 6)
  unfold cells lt
  ipra_le sl hp

def output (p A R : PTm n) : PTm n := pairT (etaDen p A R)
  (pairT (top p A R) (pairT (lipschitz p A R) (pairT (cells p A R) (height p A R))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (p A R : PTm n) : PTm n := PTm.app outputF ![p,A,R]

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p A R : PTm n) :
    Syn.subst σ (output p A R) = output (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [output, etaDen, top, lipschitz, cells, meshCost, height, tailCoefficient]

theorem program_at (p A R : PTm n) : Γ ⊢[PRAAx] run p A R ≐ output p A R := by
  simpa [run, outputF] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![p,A,R]

theorem actual_euler_integral_cutoff_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

theorem euler_integral_omitted_tail_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (((var 1)+tailCoefficient (var 2))*unit ((var 0)+num 6)) (unit (height (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (omitted_tail_budget _ _ _)

theorem euler_integral_compact_mesh_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (cells (var 0) (var 1) (var 2)) ⋏
      lt (meshCost (var 0) (var 1) (var 2)*unit ((var 0)+num 6)) (cells (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (mesh_positive _ _ _) (mesh_error_budget _ _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaIntegralCutoffs
