import FabiusFunction.LambertWElementaryBounds

/-!
# The Cayley tree function

The transseries volume's `p1:def:cayley`: the solution of `C = w e^C` with
`C(0) = 0`, and its identification with the principal Lambert branch,

`C(w) = -W₀(-w)`.

The corpus takes that identification as the *definition*, which makes
`p1:eq:cayley-lambert` a rewriting step and leaves the functional equation, the
initial condition, monotonicity and the value at the singularity as short
consequences of the Lambert API.  Reading it the other way round,
`principalLambertW_eq_neg_cayleyTree` expresses `W₀` through `C`.

Domain.  The real principal branch is defined on `[-e⁻¹, ∞)`, so `C(w)` is
meaningful for `w ≤ e⁻¹`, and that is the hypothesis carried throughout.  The
volume's analyticity on `|w| < e⁻¹` is a complex statement and is not
formalized; what is formal here is the real function on `(-∞, e⁻¹]`, on which
it is strictly increasing, and the boundary value `C(e⁻¹) = 1`, the point where
the tree function reaches the branch point of `W₀` and its own singularity.

Uniqueness carries the branch condition explicitly: `cayleyTree_unique` asks
`c ≤ 1`, which is `-c ≥ -1`, the principal-branch side of `W₀`.  Without it the
functional equation `c = w e^c` has a second solution for `0 < w < e⁻¹`, coming
from the lower branch, and the statement would be false.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- **`p1:def:cayley`.**  The Cayley tree function, defined through the
principal Lambert branch as in `p1:eq:cayley-lambert`. -/
noncomputable def cayleyTree (w : ℝ) : ℝ := -principalLambertW (-w)

/-- **`p1:eq:cayley-lambert`, read as a statement about `W₀`.** -/
theorem principalLambertW_eq_neg_cayleyTree (z : ℝ) :
    principalLambertW z = -cayleyTree (-z) := by
  rw [cayleyTree, neg_neg, neg_neg]

/-- **The functional equation** `C(w) = w e^{C(w)}`, for `w ≤ e⁻¹`. -/
theorem cayleyTree_eq_mul_exp {w : ℝ} (hw : w ≤ Real.exp (-1)) :
    cayleyTree w = w * Real.exp (cayleyTree w) := by
  have hdom : -Real.exp (-1) ≤ -w := by linarith
  have hkey := principalLambertW_mul_exp hdom
  have hexp : Real.exp (cayleyTree w) * Real.exp (principalLambertW (-w)) = 1 := by
    rw [cayleyTree, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hw' : w = -(principalLambertW (-w) * Real.exp (principalLambertW (-w))) := by
    rw [hkey, neg_neg]
  rw [cayleyTree]
  nth_rewrite 2 [hw']
  rw [cayleyTree] at hexp
  nlinarith [hexp, Real.exp_pos (-principalLambertW (-w))]

/-- `C(0) = 0`, the initial condition. -/
@[simp] theorem cayleyTree_zero : cayleyTree 0 = 0 := by
  rw [cayleyTree, neg_zero, principalLambertW_zero, neg_zero]

/-- `C` is nonnegative on `[0, e⁻¹]`. -/
theorem cayleyTree_nonneg {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ Real.exp (-1)) :
    0 ≤ cayleyTree w := by
  have hmem : -w ∈ Icc (-Real.exp (-1)) 0 := ⟨by linarith, by linarith⟩
  have := principalLambertW_nonpos hmem
  rw [cayleyTree]
  linarith

/-- **The value at the singularity**: `C(e⁻¹) = 1`, the point where the tree
function reaches the branch point of `W₀`. -/
@[simp] theorem cayleyTree_exp_neg_one : cayleyTree (Real.exp (-1)) = 1 := by
  rw [cayleyTree, principalLambertW_branchPoint, neg_neg]

/-- `C` is strictly increasing on its real domain `(-∞, e⁻¹]`. -/
theorem cayleyTree_strictMonoOn : StrictMonoOn cayleyTree (Iic (Real.exp (-1))) := by
  intro a ha b hb hab
  have hA : -Real.exp (-1) ≤ -a := by
    have := mem_Iic.mp ha; linarith
  have hB : -Real.exp (-1) ≤ -b := by
    have := mem_Iic.mp hb; linarith
  have := principalLambertW_strictMonoOn (mem_Ici.mpr hB) (mem_Ici.mpr hA)
    (by linarith : -b < -a)
  rw [cayleyTree, cayleyTree]
  linarith

/-- `C(w) ≤ 1` on the real domain, with equality only at the singularity. -/
theorem cayleyTree_le_one {w : ℝ} (hw : w ≤ Real.exp (-1)) : cayleyTree w ≤ 1 := by
  rw [← cayleyTree_exp_neg_one]
  exact cayleyTree_strictMonoOn.monotoneOn (mem_Iic.mpr hw) (mem_Iic.mpr le_rfl) hw

/-- **Uniqueness on the principal branch.**  A solution of `c = w e^c` with
`c ≤ 1` is `C(w)`.  The bound `c ≤ 1` is the branch condition and cannot be
dropped: for `0 < w < e⁻¹` the equation has a second, larger root. -/
theorem cayleyTree_unique {w c : ℝ} (hw : w ≤ Real.exp (-1)) (hc : c ≤ 1)
    (heq : c = w * Real.exp c) : c = cayleyTree w := by
  have hdom : -Real.exp (-1) ≤ -w := by linarith
  have hmul : (-c) * Real.exp (-c) = -w := by
    have hexp : Real.exp c * Real.exp (-c) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nth_rewrite 1 [heq]
    nlinarith [hexp]
  have := principalLambertW_unique hdom (by linarith : (-1 : ℝ) ≤ -c) hmul
  rw [cayleyTree, ← this, neg_neg]

end Fabius
