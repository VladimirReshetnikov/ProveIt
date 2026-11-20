import ContinuousMeasure

open IPRAContinuousMeasure

/-! Exact rational sanity checks; these do not replace the general proofs. -/

/-- The old separate-tail split fails at x=2, y=-1, K=1. -/
example : ¬((2 - (-1) : Rat).abs ≤
    (if (2 : Rat).abs ≤ 1 ∧ (-1 : Rat).abs ≤ 1 then (2 - (-1) : Rat).abs else 0) +
    (if 1 < (2 : Rat).abs then (2 : Rat).abs else 0) +
    (if 1 < (-1 : Rat).abs then (-1 : Rat).abs else 0)) := by
  have h₁ : (2 : Rat).abs = 2 := Rat.abs_of_nonneg (by grind)
  have h₂ : (-1 : Rat).abs = 1 := by
    rw [Rat.abs_of_nonpos (by grind)]
    grind
  have h₃ : (2 - (-1) : Rat).abs = 3 := by
    rw [Rat.abs_of_nonneg (by grind)]
    grind
  rw [h₁, h₂, h₃]
  grind

/-- The corrected clipping inequality covers that same boundary case. -/
example : (2 - (-1) : Rat).abs ≤ tail 1 2 + tail 1 (-1) +
    2 * (1 : Rat) * cappedDistance 2 (-1) :=
  scalar_vitali_unit (by grind)

/-- A two-atom expectation computes exactly, without floating-point data. -/
example : integrate 2 (fun _ => (1 / 2 : Rat))
    (fun i => if i = 0 then 2 else 4) = 3 := by
  simp only [integrate, qsum]
  grind

/-- A nontrivial denominator-changing mass perturbation instance. -/
example : Within (1 / 3 : Rat)
    (integrate 2 (fun _ => (1 / 2 : Rat)) (fun i => if i = 0 then 0 else 1))
    (integrate 2 (fun i => if i = 0 then (1 / 3 : Rat) else 2 / 3)
      (fun i => if i = 0 then 0 else 1)) := by
  unfold Within
  simp only [integrate, qsum]
  constructor <;> grind
