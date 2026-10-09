import GowersSzemeredi.Proofs16ColumnRelationCounting

/-! Choose a largest relation star independently in every finite fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- A relation on each fibre admits stars whose total number of leaves
is at least the total number of edges divided by the fibre size. -/
theorem exists_large_fibre_stars {D V : Type*} [Fintype D] [Fintype V] [Nonempty V]
    (R : D → V → V → Prop) :
    ∃ c : D → V,
      (Finset.univ.filter (fun t : D × V × V => R t.1 t.2.1 t.2.2)).card ≤
        Fintype.card V * (Finset.univ.filter (fun t : D × V => R t.1 (c t.1) t.2)).card := by
  let deg (d : D) (a : V) := (Finset.univ.filter (R d a)).card
  have hmax : ∀ d, ∃ a : V, ∀ b : V, deg d b ≤ deg d a := by
    intro d
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (deg d) Finset.univ_nonempty
    exact ⟨a, fun b => ha b (Finset.mem_univ _)⟩
  choose c hc using hmax
  refine ⟨c, ?_⟩
  have hleft : (Finset.univ.filter (fun t : D × V × V => R t.1 t.2.1 t.2.2)).card =
      ∑ d : D, ∑ a : V, deg d a := by
    simp only [deg, Finset.card_filter, Fintype.sum_prod_type]
  have hright : (Finset.univ.filter (fun t : D × V => R t.1 (c t.1) t.2)).card =
      ∑ d : D, deg d (c d) := by
    simp only [deg, Finset.card_filter, Fintype.sum_prod_type]
  rw [hleft, hright, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  calc (∑ a : V, deg d a) ≤ ∑ _a : V, deg d (c d) :=
      Finset.sum_le_sum fun a _ => hc d a
    _ = Fintype.card V * deg d (c d) := by simp

end LeanProofs.GowersSzemeredi
