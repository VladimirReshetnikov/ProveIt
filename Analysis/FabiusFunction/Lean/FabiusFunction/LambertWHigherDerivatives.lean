import FabiusFunction.AutonomousIteratedDeriv
import FabiusFunction.PrincipalLambertW
import FabiusFunction.LowerLambertW
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# All derivatives of the real Lambert branches

Both real branches satisfy the autonomous equation `W' = e^{-W}/(1+W)`, so by
`AutonomousODE.iteratedDeriv_eq_comp` every derivative is a function of `W`:

`W^{(n+1)}(x) = e^{-(n+1)W(x)} · P_n(W(x)) / (1+W(x))^{2n+1}`,

with polynomials `P_n` given by the recurrence

`P_0 = 1,  P_{n+1} = (1+w)·P_n' - ((n+1)w + 3n+2)·P_n`.

This is the "polynomial recurrence for all derivatives" theorem of the
Lambert W guide, whose `P_n` is our `P_{n-1}`:
`P_1 = 1`, `P_2 = -(w+2)`, `P_3 = 2w²+8w+9`.  The guide proves it for both
branches at once, and so does the formalization: the only branch-specific
input is the first derivative, and the only property of the branch used
beyond it is `W ≠ -1` on the open domain.

The mechanism is the general lemma; what is specific here is one derivative
computation — that `G_n(w) = e^{-nw}P_{n-1}(w)/(1+w)^{2n-1}` has derivative
`e^{-nw}P_n(w)/(1+w)^{2n}` — which is exactly the recurrence, and is proved
once for every real `w ≠ -1`.
-/

set_option autoImplicit false

open Polynomial Set

namespace Fabius

/-! ### The derivative polynomials -/

/-- The Lambert derivative polynomials: `P_0 = 1` and
`P_{n+1} = (1+X)·P_n' - ((n+1)X + (3n+2))·P_n`.  In the guide's numbering
this is `P_{n+1}`. -/
noncomputable def lambertDerivPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + X) * derivative (lambertDerivPoly n) -
        ((n + 1 : ℝ[X]) * X + (3 * n + 2 : ℝ[X])) * lambertDerivPoly n

/-- The zeroth Lambert derivative polynomial is one. -/
@[simp] theorem lambertDerivPoly_zero : lambertDerivPoly 0 = 1 := rfl

/-- The defining recurrence for the Lambert derivative polynomials. -/
theorem lambertDerivPoly_succ (n : ℕ) :
    lambertDerivPoly (n + 1) =
      (1 + X) * derivative (lambertDerivPoly n) -
        ((n + 1 : ℝ[X]) * X + (3 * n + 2 : ℝ[X])) * lambertDerivPoly n := rfl

/-- The recurrence, evaluated at a point. -/
theorem eval_lambertDerivPoly_succ (n : ℕ) (w : ℝ) :
    (lambertDerivPoly (n + 1)).eval w =
      (1 + w) * (derivative (lambertDerivPoly n)).eval w -
        ((n + 1) * w + (3 * n + 2)) * (lambertDerivPoly n).eval w := by
  rw [lambertDerivPoly_succ]
  simp [eval_sub, eval_mul, eval_add, eval_X, eval_one, eval_natCast]

/-- `P_1 = -(w + 2)`, the guide's `P_2`. -/
theorem eval_lambertDerivPoly_one (w : ℝ) :
    (lambertDerivPoly 1).eval w = -(w + 2) := by
  simp [eval_lambertDerivPoly_succ] <;> ring

/-- `P_2 = 2w² + 8w + 9`, the guide's `P_3`. -/
theorem eval_lambertDerivPoly_two (w : ℝ) :
    (lambertDerivPoly 2).eval w = 2 * w ^ 2 + 8 * w + 9 := by
  rw [eval_lambertDerivPoly_succ]
  have hd : derivative (lambertDerivPoly 1) = -1 := by
    rw [lambertDerivPoly_succ]
    simp
  rw [hd, eval_lambertDerivPoly_one]
  simp <;> ring

/-! ### The derivative functions and their one calculus fact -/

/-- `G_n(w) = e^{-nw}·P_{n-1}(w)/(1+w)^{2n-1}` for `n ≥ 1`, and `G_0 = id`. -/
noncomputable def lambertDerivFun : ℕ → ℝ → ℝ
  | 0 => fun w => w
  | n + 1 => fun w =>
      Real.exp (-((n + 1 : ℝ) * w)) * (lambertDerivPoly n).eval w / (1 + w) ^ (2 * n + 1)

/-- The claimed derivative of `G_n`: `G_0' = 1` and
`G_{n+1}'(w) = e^{-(n+1)w}·P_{n+1}(w)/(1+w)^{2n+2}`. -/
noncomputable def lambertDerivFun' : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun w =>
      Real.exp (-((n + 1 : ℝ) * w)) * (lambertDerivPoly (n + 1)).eval w / (1 + w) ^ (2 * n + 2)

/-- The branch equation's right-hand side: `φ(w) = (e^w (w+1))⁻¹`. -/
noncomputable def lambertPhi (w : ℝ) : ℝ := (Real.exp w * (w + 1))⁻¹

/-- **The recurrence step**: `G_{n+1} = G_n' · φ` pointwise, for `w ≠ -1`. -/
theorem lambertDerivFun_succ_eq (n : ℕ) (w : ℝ) (hw : w ≠ -1) :
    lambertDerivFun (n + 1) w = lambertDerivFun' n w * lambertPhi w := by
  have h1 : 1 + w ≠ 0 := fun h => hw (by linarith)
  have he : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
  have h2 : w + 1 ≠ 0 := fun h => hw (by linarith)
  cases n with
  | zero =>
    simp only [lambertDerivFun, lambertDerivFun', lambertPhi, lambertDerivPoly_zero, eval_one]
    field_simp
    rw [← Real.exp_add]
    simp <;> first | rfl | ring
  | succ n =>
    simp only [lambertDerivFun, lambertDerivFun', lambertPhi]
    set P := (lambertDerivPoly (n + 1)).eval w with hP
    push_cast
    have hx : Real.exp (-w) * Real.exp w = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [show -(((n : ℝ) + 1 + 1) * w) = -(((n : ℝ) + 1) * w) + -w by ring, Real.exp_add,
      show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring, pow_succ]
    field_simp
    linear_combination (w * P + P) * hx

/-- **The one calculus fact**: `G_{n}` has derivative `G_n'` at every `w ≠ -1`. -/
theorem hasDerivAt_lambertDerivFun (n : ℕ) (w : ℝ) (hw : w ≠ -1) :
    HasDerivAt (lambertDerivFun n) (lambertDerivFun' n w) w := by
  have h1 : 1 + w ≠ 0 := fun h => hw (by linarith)
  cases n with
  | zero =>
    show HasDerivAt (fun w : ℝ => w) 1 w
    exact hasDerivAt_id' w
  | succ n =>
    -- `G_{n+1} = (e^{-(n+1)w} · P_n(w)) / (1+w)^{2n+1}`: the quotient rule
    have hexp : HasDerivAt (fun w : ℝ => Real.exp (-((n + 1 : ℝ) * w)))
        (Real.exp (-((n + 1 : ℝ) * w)) * (-(n + 1 : ℝ))) w := by
      have := (((hasDerivAt_id' w).const_mul ((n + 1 : ℝ))).neg).exp
      simpa using this
    have hpoly : HasDerivAt (fun w : ℝ => (lambertDerivPoly n).eval w)
        ((derivative (lambertDerivPoly n)).eval w) w :=
      (lambertDerivPoly n).hasDerivAt w
    have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (2 * n + 1))
        (((2 * n + 1 : ℕ) : ℝ) * (1 + w) ^ (2 * n) * 1) w :=
      ((hasDerivAt_id' w).const_add 1).pow (2 * n + 1)
    have hne : (1 + w) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ h1
    have hG : lambertDerivFun (n + 1) = fun w : ℝ =>
        (Real.exp (-((n + 1 : ℝ) * w)) * (lambertDerivPoly n).eval w) /
          (1 + w) ^ (2 * n + 1) := by
      funext w
      simp only [lambertDerivFun]
    rw [hG]
    refine ((hexp.mul hpoly).div hden hne).congr_deriv ?_
    -- the derivative expression is the recurrence
    simp only [lambertDerivFun', eval_lambertDerivPoly_succ, Pi.mul_apply]
    push_cast
    field_simp
    ring

/-! ### All derivatives of both branches -/

/-- **All derivatives of the principal branch**: for `x > -1/e`,
`W₀^{(n+1)}(x) = e^{-(n+1)W₀(x)} · P_n(W₀(x)) / (1+W₀(x))^{2n+1}`. -/
theorem iteratedDeriv_principalLambertW (n : ℕ) {x : ℝ} (hx : -Real.exp (-1) < x) :
    iteratedDeriv (n + 1) principalLambertW x =
      Real.exp (-((n + 1 : ℝ) * principalLambertW x)) *
        (lambertDerivPoly n).eval (principalLambertW x) /
          (1 + principalLambertW x) ^ (2 * n + 1) := by
  have hne : ∀ y ∈ Ioi (-Real.exp (-1)), principalLambertW y ≠ -1 := fun y hy =>
    ne_of_gt (neg_one_lt_principalLambertW (mem_Ioi.mp hy))
  exact AutonomousODE.iteratedDeriv_eq_comp (s := Ioi (-Real.exp (-1)))
    (W := principalLambertW) (φ := lambertPhi) isOpen_Ioi
    (fun y hy => principalLambertW_hasDerivAt (mem_Ioi.mp hy))
    lambertDerivFun lambertDerivFun' (fun _ _ => rfl)
    (fun m y hy => hasDerivAt_lambertDerivFun m _ (hne y hy))
    (fun m y hy => lambertDerivFun_succ_eq m _ (hne y hy)) (n + 1) x (mem_Ioi.mpr hx)

/-- **All derivatives of the lower branch**: for `-1/e < x < 0`,
`W₋₁^{(n+1)}(x) = e^{-(n+1)W₋₁(x)} · P_n(W₋₁(x)) / (1+W₋₁(x))^{2n+1}`, with the
same polynomials. -/
theorem iteratedDeriv_lowerLambertW (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    iteratedDeriv (n + 1) lowerLambertW x =
      Real.exp (-((n + 1 : ℝ) * lowerLambertW x)) *
        (lambertDerivPoly n).eval (lowerLambertW x) /
          (1 + lowerLambertW x) ^ (2 * n + 1) := by
  have hne : ∀ y ∈ Ioo (-Real.exp (-1)) 0, lowerLambertW y ≠ -1 := fun y hy =>
    ne_of_lt (lowerLambertW_lt_neg_one hy)
  exact AutonomousODE.iteratedDeriv_eq_comp (s := Ioo (-Real.exp (-1)) 0)
    (W := lowerLambertW) (φ := lambertPhi) isOpen_Ioo
    (fun y hy => lowerLambertW_hasDerivAt hy)
    lambertDerivFun lambertDerivFun' (fun _ _ => rfl)
    (fun m y hy => hasDerivAt_lambertDerivFun m _ (hne y hy))
    (fun m y hy => lambertDerivFun_succ_eq m _ (hne y hy)) (n + 1) x hx

end Fabius
