import FabiusFunction.LambertShiftInverse
import FabiusFunction.LambertWCurvature

/-!
# Concavity of `x ↦ x + W(x)`, and the certificate in sandwich form

Two loose ends of the transseries volume's `q1:prop:brackets` and
`q1:prop:certificate`.

The concavity of `f(x) = x + W(x)` was the one clause of `q1:prop:brackets`
with no formal counterpart: the corpus had the strict concavity of the branch
itself (`strictConcaveOn_principalLambertW`) and the strict *convexity* of the
inverse `g` (`strictConvexOn_lambertShiftInv`, obtained from the derivative),
but not the concavity of `f`.  It is immediate once one notices that adding the
identity to a strictly concave function keeps it strictly concave, and it comes
out on the *full* closed domain `[-e⁻¹, ∞)` rather than only on `[0, ∞)`, since
that is where the branch is concave.

The certificate is then restated in the exact shape of the volume's display: a
single two-sided sandwich `|R|/2 ≤ |x̃ - g(z)| ≤ |R|` together with the sign
agreement between the residual and the error.  Both halves already exist
separately in `LambertShiftInverse.lean`; what is added is the conjunction the
volume states, so that a reader can match the display to one name.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ### Concavity of the shifted map -/

/-- **`q1:prop:brackets`, concavity clause.**  `f(x) = x + W(x)` is strictly
concave on the whole closed domain of the principal branch.  Note the domain:
the volume states concavity on `(0,∞)`, but nothing in the argument needs
positivity — the identity contributes an equality to the concavity inequality
and the branch supplies the strict part. -/
theorem strictConcaveOn_lambertShift :
    StrictConcaveOn ℝ (Ici (-Real.exp (-1))) lambertShift := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hW := strictConcaveOn_principalLambertW.2 hx hy hxy ha hb hab
  simp only [lambertShift, smul_eq_mul] at hW ⊢
  have hkey : a * (x + principalLambertW x) + b * (y + principalLambertW y) =
      a * x + b * y + (a * principalLambertW x + b * principalLambertW y) := by ring
  rw [hkey]
  linarith

/-- The same on the half-line the volume works with. -/
theorem strictConcaveOn_lambertShift_Ici_zero :
    StrictConcaveOn ℝ (Ici (0 : ℝ)) lambertShift :=
  strictConcaveOn_lambertShift.subset
    (fun _ hx => mem_Ici.mpr (neg_exp_neg_one_le_of_nonneg (mem_Ici.mp hx))) (convex_Ici _)

/-! ### The residual certificate in the volume's shape -/

/-- **`q1:eq:sandwich`.**  For any candidate `x̃ ≥ 0` with residual
`R = f(x̃) - z`, the error is trapped on both sides:
`|R|/2 ≤ |x̃ - g(z)| ≤ |R|`.  The two halves are
`abs_residual_le_two_mul_abs_sub_lambertShiftInv` and
`abs_sub_lambertShiftInv_le_abs_residual`; this is the conjunction the volume
displays. -/
theorem abs_sub_lambertShiftInv_sandwich {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    |lambertShift x - z| / 2 ≤ |x - lambertShiftInv z| ∧
      |x - lambertShiftInv z| ≤ |lambertShift x - z| := by
  refine ⟨?_, abs_sub_lambertShiftInv_le_abs_residual hz hx⟩
  have := abs_residual_le_two_mul_abs_sub_lambertShiftInv hz hx
  linarith

/-- **`q1:prop:certificate`, sign clause.**  The residual and the error have the
same sign, in the two-sided form: the residual is positive exactly when the
candidate overshoots and negative exactly when it undershoots. -/
theorem residual_sign_agrees {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    (0 < lambertShift x - z ↔ 0 < x - lambertShiftInv z) ∧
      (lambertShift x - z < 0 ↔ x - lambertShiftInv z < 0) := by
  constructor
  · rw [residual_pos_iff hz hx, sub_pos]
  · rw [residual_neg_iff hz hx, sub_neg]

/-- Zero residual pins the candidate exactly: the certificate is sharp at the
root as well as away from it. -/
theorem residual_eq_zero_iff {z x : ℝ} (hz : 0 ≤ z) (hx : 0 ≤ x) :
    lambertShift x - z = 0 ↔ x = lambertShiftInv z := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd ((residual_neg_iff hz hx).mpr hlt) (by rw [h]; exact lt_irrefl 0)
    · exact absurd ((residual_pos_iff hz hx).mpr hgt) (by rw [h]; exact lt_irrefl 0)
  · intro h
    rw [h, lambertShift_lambertShiftInv hz, sub_self]

end Fabius
