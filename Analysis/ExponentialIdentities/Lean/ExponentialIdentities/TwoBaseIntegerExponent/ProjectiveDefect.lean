import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# Projective Padé-defect optimization

This module formalizes the finite real-inequality core of report 25's
representation-independent upper bound for Kawashima's weight-two defect.
The number-field height identities and Kawashima's transcendence theorem remain
external paper inputs.
-/

namespace ProjectiveDefect

/-- The abstract affine expression occurring in the weight-two defect after
the analytic constants have been named. -/
def padeDefect (D C t A H X Y : ℝ) : ℝ :=
  (D + 1) * t - A - D * (H + X + Y) - C

/-- Exact piecewise-linear optimization behind the projective defect bound.
When `a ≤ P`, every choice of the common local scaling variable `t` is bounded
by the value attained throughout the interval `[a,P]`. -/
theorem piecewise_projective_bound
    (D t a P : ℝ) (hD : 0 ≤ D) (haP : a ≤ P) :
    (D + 1) * t - (D + 1) * max 0 (t - a) - D * max t P ≤
      (D + 1) * a - D * P := by
  by_cases hta : t ≤ a
  · rw [max_eq_left (sub_nonpos.mpr hta), max_eq_right (hta.trans haP)]
    nlinarith
  · have hat : a ≤ t := le_of_not_ge hta
    rw [max_eq_right (sub_nonneg.mpr hat)]
    by_cases htP : t ≤ P
    · rw [max_eq_right htP]
      ring_nf
      exact le_rfl
    · have hPt : P ≤ t := le_of_not_ge htP
      rw [max_eq_left hPt]
      nlinarith

/-- Abstract projective defect theorem.  The hypotheses are precisely the
elementary local/global height inequalities used in the paper proof:

* `A = max 0 (t-a)` is the local vector height;
* `t ≤ H` and `P ≤ X+H` are scalar-height bounds;
* `A ≤ Y` is the global vector-height bound;
* `a ≤ P` is the reciprocal local-height bound for the points.
-/
theorem padeDefect_le_projective
    (D C t a P A H X Y : ℝ)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (haP : a ≤ P)
    (hA : A = max 0 (t - a)) (htH : t ≤ H)
    (hP : P ≤ X + H) (hY : A ≤ Y) :
    padeDefect D C t A H X Y ≤ (D + 1) * a - D * P - C := by
  have htHX : t ≤ H + X := by linarith
  have hPHX : P ≤ H + X := by linarith
  have hmax : max t P ≤ H + X := max_le htHX hPHX
  have hbudget : max t P + A ≤ H + X + Y := by linarith
  have hmul : D * (max t P + A) ≤ D * (H + X + Y) :=
    mul_le_mul_of_nonneg_left hbudget hD
  calc
    padeDefect D C t A H X Y ≤
        (D + 1) * t - A - D * (max t P + A) - C := by
      dsimp [padeDefect]
      linarith
    _ = (D + 1) * t - (D + 1) * A - D * max t P - C := by ring
    _ = (D + 1) * t - (D + 1) * max 0 (t - a) - D * max t P - C := by
      rw [hA]
    _ ≤ (D + 1) * a - D * P - C := by
      linarith [piecewise_projective_bound D t a P hD haP]

/-- Positivity of a quantity below the projective bound forces both the depth
and arithmetic-efficiency thresholds from report 25. -/
theorem depth_and_efficiency_threshold
    (D C a P V : ℝ) (hD : 0 < D) (hC : 0 ≤ C)
    (hPpos : 0 < P) (haP : a ≤ P) (hV : 0 < V)
    (hbound : V ≤ (D + 1) * a - D * P - C) :
    C < a ∧ D / (D + 1) < a / P ∧ P < (1 + 1 / D) * a := by
  have hD0 : 0 ≤ D := le_of_lt hD
  have hDP : D * a ≤ D * P := mul_le_mul_of_nonneg_left haP hD0
  have hpositive : 0 < (D + 1) * a - D * P - C := lt_of_lt_of_le hV hbound
  have hdepth : C < a := by linarith
  have hmass : D * P < (D + 1) * a := by linarith
  have hD1 : 0 < D + 1 := by linarith
  have heff : D / (D + 1) < a / P := by
    rw [div_lt_div_iff₀ hD1 hPpos]
    nlinarith
  have hupper : P < (1 + 1 / D) * a := by
    calc
      P = (D * P) / D := by field_simp [ne_of_gt hD]
      _ < ((D + 1) * a) / D := div_lt_div_of_pos_right hmass hD
      _ = (1 + 1 / D) * a := by field_simp [ne_of_gt hD]
  exact ⟨hdepth, heff, hupper⟩

end ProjectiveDefect

end LeanProofs.TwoBaseIntegerExponent
