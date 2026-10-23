import DiophantineConsistency.NativeSparseBounds52

open DiophantineConsistency NativeSparseBounds52
open scoped BigOperators

/-- Check the selected actual weights and omitted dummy position. -/
example : inputWeights 4 = 174 ∧ inputWeights 1 = 169 ∧ inputWeights 6 = 0 := by decide
example : ∀ i, inputWeights i ≠ 81 := dummy_excluded

/-- A zero at weight zero still contributes a genuine input digit; setting
that input to one gives code one, independently of the radix. -/
example (B : ℕ) : code B (fun i => if i = 6 then 1 else 0) = 1 := by
  unfold code LowMaskCoding.indexedCode
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [input_zero_weight, pow_zero]

/-- The restriction `b≤B` in the sharp bound is necessary. These two actual
positions already give a counterexample without it. -/
private def tooWide : Fin 31 → ℕ := fun i => if i = 4 ∨ i = 1 then 99 else 0

example : (∀ i, tooWide i < 100) ∧ 100 * 2 ^ 174 < code 2 tooWide := by decide

example (ports : Fin 4 → ℤ) :
    NativeQuadraticParent.sourceRows ports (fun _ : Fin 31 => (1 : ℤ)) 4 ≠ 0 := by
  rw [source_row4_at_one]
  decide

#print axioms code_lt_mul_pow
#print axioms source_row4_at_one
#print axioms source_zero_ne_zero
#print axioms code_eq_zero_iff
#print axioms source_zero_code_pos
#print axioms source_zero_code_bounds
