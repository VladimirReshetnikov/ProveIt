import OAI.Combinatorics.Progressions.Dynamics.ReplacementCellPotential

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem cellAverage_le_shifted (C : Finset G) (f F : G → ℝ) (x : G)
    (hF : ∀ r, F r ≤ f (x + r)) (z : G) :
    cellAverage C F z ≤ cellAverage C f (x + z) := by
  unfold cellAverage
  apply Finset.expect_le_expect
  intro c _
  simpa only [add_assoc] using hF (z + c)

omit [Fintype G] in
theorem translated_slice_le (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : Peeling.slice L (fun t => f (x + t)) r ≤ f (x + r) := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem translated_slice_nonneg (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : 0 ≤ Peeling.slice L (fun t => f (x + t)) r := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem expect_translated_slice (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, Peeling.slice L (fun t => f (x + t)) r) = cellAverage L f x := by
  apply Finset.expect_congr rfl
  intro r hr
  simp only [Peeling.slice, hr, ite_true]

omit [Fintype G] [DecidableEq G] in
theorem normalized_local_cell_cap (C : Finset G) (f F : G → ℝ) (x : G)
    (hF : ∀ r, F r ≤ f (x + r)) {u u₀ c₀ K : ℝ}
    (hu : 0 < u) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hlower : c₀ * u ≤ u₀)
    (hparent : ∀ z, cellAverage C f z ≤ K * u) (z : G) :
    cellAverage C F z / u₀ ≤ K / c₀ :=
  normalized_cell_cap hu hc₀ hK hlower ((cellAverage_le_shifted C f F x hF z).trans
    (hparent (x + z)))

end Erdos3

end

end OAI
