import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-! Semantic certificate core for geometric separation of a rational PL map.
`PairValue.source` and `.target` are values of the two affine distances on
one cell. The finite enumeration of geometric cells and vertices, and its
internalization as an ordinary iPRA proof, are further obligations. -/
namespace PairBounds

structure PairValue where
  source : ℚ
  target : ℚ

def checkLower (c : ℚ) (vs : List PairValue) : Bool :=
  vs.all (fun v => decide (c * v.source ≤ v.target))

inductive Mix (vs : List PairValue) : PairValue → Prop where
  | vertex {v} : v ∈ vs → Mix vs v
  | split {x y} (t : ℚ) : 0 ≤ t → t ≤ 1 → Mix vs x → Mix vs y →
      Mix vs ⟨t*x.source + (1-t)*y.source, t*x.target + (1-t)*y.target⟩

theorem lower_of_mix {c : ℚ} {vs : List PairValue} {v : PairValue}
    (h : checkLower c vs = true) (hm : Mix vs v) : c*v.source ≤ v.target := by
  induction hm with
  | vertex hv =>
      have h' := List.all_eq_true.mp h _ hv
      exact of_decide_eq_true h'
  | split t ht hu _ _ hx hy =>
      dsimp
      have h₁ := mul_le_mul_of_nonneg_left hx ht
      have h₂ := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hu)
      linarith only [h₁, h₂]

/-- Any attained positive-denominator equality certifies sharpness. -/
theorem extremal_bound {c other : ℚ} {v : PairValue} (hp : 0 < v.source)
    (tight : v.target = c*v.source) (valid : other*v.source ≤ v.target) : other ≤ c := by
  rw [tight] at valid
  exact (mul_le_mul_iff_left₀ hp).mp valid

/-- Arithmetic used with a pairwise Lipschitz perturbation. -/
theorem perturbation {d old newD c defect : ℚ} (hl : c*d ≤ old)
    (he : old ≤ newD + defect*d) : (c-defect)*d ≤ newD := by
  linarith only [hl,he]

/-- Arithmetic used with a pair of uniformly accurate point evaluations. -/
theorem uniform_error {d old newD c e : ℚ} (hl : c*d ≤ old)
    (he : old ≤ newD + 2*e) : c*d-2*e ≤ newD := by
  linarith only [hl,he]

end PairBounds
