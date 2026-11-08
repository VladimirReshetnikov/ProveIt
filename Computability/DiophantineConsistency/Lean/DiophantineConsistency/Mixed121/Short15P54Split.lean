import DiophantineConsistency.Mixed121.Short15Units

/-! # Package 54's fifteen-positive finalizer: `A² + B(B − 2) + C²`

Package 54's 70 / 80, 71 / 78 and 72 / 64 gate lists end in
`A² + B(B − 2) + C²` with `A = N0·N1`, `B = Na·Nk·Nt` and `C` the ordinary strong
residual. Since `B(B − 2) = (B − 1)² − 1`, a zero is `A² + (B − 1)² + C² = 1`.
In the ring of differences of a model of `𝗜𝚺₁` (discrete), `A ≠ 0` forces
`A = ±1`, `B = 1` and `C = 0`; the excluded values of `Short15Units` then give
`N0 = N1 = Na = 1` and `Nk = Nt = ±1`, the same residual state as the
six-factor products of packages 59 and 56. -/
set_option autoImplicit false
noncomputable section
namespace Short15P54Split
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing DiscreteOrderedRingFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem one_le_sq {x : DiffRing V} (hx : x ≠ 0) : 1 ≤ x * x := by
  have h1 : 1 ≤ |x| := abs_ge_one ModelArithmetic.model_discrete hx
  have := abs_mul_abs_self x
  nlinarith [abs_nonneg x]

/-- A zero of `a² + b(b − 2) + s²` with `a ≠ 0` has `a = ±1`, `b = 1`, `s = 0`. -/
theorem falling {a b s : DiffRing V} (h : a * a + b * (b - 2) + s * s = 0) (ha : a ≠ 0) :
    (a = 1 ∨ a = -1) ∧ b = 1 ∧ s = 0 := by
  have e : 1 ≤ a * a := one_le_sq ha
  have h' : a * a + (b - 1) * (b - 1) + s * s = 1 := by linear_combination h
  have hb := mul_self_nonneg (b - 1)
  have hs := mul_self_nonneg s
  have haa : a * a = 1 := by linarith
  have hbb : (b - 1) * (b - 1) = 0 := by linarith
  have hss : s * s = 0 := by linarith
  exact ⟨eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete haa,
    sub_eq_zero.mp (mul_self_eq_zero.mp hbb), mul_self_eq_zero.mp hss⟩

/-- The residual state at a zero of package 54's finalizer. -/
theorem split {n0 n1 na nk nt s : DiffRing V}
    (h : n0 * n1 * (n0 * n1) + na * nk * nt * (na * nk * nt - 2) + s * s = 0)
    (h0 : n0 ≠ 0) (h1 : n1 ≠ 0) (h0' : n0 ≠ -1) (h1' : n1 ≠ -1) (ha : na ≠ -1) :
    n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ s = 0 ∧ ((nk = 1 ∧ nt = 1) ∨ (nk = -1 ∧ nt = -1)) := by
  obtain ⟨hA, hB, hs⟩ := falling h (mul_ne_zero h0 h1)
  have u01 := Short15Units.unit_pm hA
  have hB' : na * (nk * nt) = 1 := by rw [← mul_assoc]; exact hB
  have ua := Short15Units.unit_pm (Or.inl hB')
  have ea : na = 1 := ua.1.resolve_right ha
  rw [ea, one_mul] at hB'
  exact ⟨u01.1.resolve_right h0', u01.2.resolve_right h1', ea, hs, Short15Units.sign_of_mul hB'⟩

end Short15P54Split

#print axioms Short15P54Split.falling
#print axioms Short15P54Split.split
