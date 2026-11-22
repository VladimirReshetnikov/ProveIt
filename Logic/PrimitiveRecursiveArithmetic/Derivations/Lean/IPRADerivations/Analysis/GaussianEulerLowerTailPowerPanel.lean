import IPRADerivations.Analysis.PowerGap
import IPRADerivations.Analysis.RationalNonnegativePowers

/-!
# A right-endpoint power panel for the lower Euler tail

For rational endpoints `u=x/D ≤ v=y/D` and positive `v`, apply the
existing power-gap bound at the right endpoint. With `A=k+1`, the
actual scalar product `(v^A-u^A)·v^(1-A)` is at most `A(v-u)`.
All terms are primitive recursive and the bound uses the original
rational order after clearing the two denominators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailPowerPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open RationalNonnegativePowers (power fraction_multiply denominator_positive)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (x y k : PTm n) : PTm n := monus (pw y (succ k)) (pw x (succ k))
def panel (x y D k : PTm n) : PTm n :=
  RationalArithmetic.multiply (fraction (width x y k) (pw D (succ k))) (power D y k)

@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (x y k : PTm n) :
    Syn.subst σ (width x y k) = width (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ k) :=
  by simp [width]

@[simp] theorem subst_panel {m : ℕ} (σ : Fin n → PTm m) (x y D k : PTm n) :
    Syn.subst σ (panel x y D k) =
      panel (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ D) (Syn.subst σ k) := by
  simp [panel,power]

theorem width_bound (x y k : PTm n) (h : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx]
    le (width x y k) (monus y x*(succ k*pw y k)) := by
  have cap := PowerGap.power_gap (eq_add_of_le h) (le_refl y) k
  have split := natEq (eq_add_of_le (pw_le_pw (succ k) h))
  unfold width
  ipra_le sl cap using linear_combination split

theorem right_panel_bound (x y D k : PTm n) (h : Γ ⊢[PRAAx] le x y)
    (hy : Γ ⊢[PRAAx] le one y) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rationalLE (panel x y D k) (fraction (succ k*monus y x) D) := by
  let U := pw D (succ k)
  let V := pw y k
  let P := pw D k
  let W := width x y k
  let A := succ k*monus y x
  have hU : Γ ⊢[PRAAx] le one U := denominator_positive D (succ k) hD
  have hV : Γ ⊢[PRAAx] le one V := denominator_positive y k hy
  have hUV := positive_product U V hU hV
  have eq : Γ ⊢[PRAAx] panel x y D k ≐ fraction (W*P) (U*V) :=
    fraction_multiply W U P V hU hV
  apply RationalArgmin.rationalLE_congr eq.eqSymm (.eqRefl _)
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hUV hD
    (RationalIntegerNormalization.normalize_preserves_value _ _ hUV)
    (RationalIntegerNormalization.normalize_preserves_value _ _ hD)
  have left : Γ ⊢[PRAAx] W*U ≐ D*(W*P) := by
    have e := natEq (pw_succ (Γ := Γ) D k)
    apply deriveNat
    dsimp only [U,P]
    ipra_simps
    rw [e]
    ring
  exact le_congr left (by dsimp only [A,V]; ipra_ring)
    (mul_le_mul_right U (width_bound x y k h))

theorem actual_Euler_lower_tail_right_panel_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le (var 0) (var 1) ⋏ le one (var 1)) ⟶ le one (var 2) ⟶
      rationalLE (panel (var 0) (var 1) (var 2) (var 3))
        (fraction (succ (var 3)*monus (var 1) (var 0)) (var 2))) :=
  closeUniv 4 (.impI (.impI (right_panel_bound _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailPowerPanel
