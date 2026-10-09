import GowersSzemeredi.Proofs16GraphNeighbourSelection

/-! Remove vertices incident to too many deficient pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- If at most one sixteenth of the ordered pairs are marked, retain
three quarters of the vertices, each with at most a quarter marked neighbours. -/
theorem exists_subset_few_marked_neighbours {V : Type*}
    (S : Finset V) (hS : S.Nonempty) (B : V → V → Prop)
    (hB : (((S ×ˢ S).filter (fun p => B p.1 p.2)).card : Real) ≤ (S.card : Real)^2/16) :
    ∃ T ⊆ S, 3*(S.card : Real)/4 ≤ T.card ∧
      ∀ u ∈ T, ((S.filter (B u)).card : Real) ≤ (S.card : Real)/4 := by
  let d (u : V) : Real := (S.filter (B u)).card
  let H (u : V) := d u ≤ (S.card : Real)/4
  let T := S.filter H
  let U := S.filter (fun u => ¬H u)
  have hsum : ∑ u ∈ S, d u = (((S ×ˢ S).filter (fun p => B p.1 p.2)).card : Real) := by
    have hnat : (∑ u ∈ S, (S.filter (B u)).card) = ((S ×ˢ S).filter (fun p => B p.1 p.2)).card := by
      simp only [Finset.card_filter, Finset.sum_product]
    dsimp only [d]
    exact_mod_cast hnat
  have hlower : (S.card : Real)/4 * U.card ≤ ∑ u ∈ U, d u := by
    calc _ = ∑ _u ∈ U, (S.card : Real)/4 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun u hu => (lt_of_not_ge (Finset.mem_filter.mp hu).2).le
  have hupper : (∑ u ∈ U, d u) ≤ ∑ u ∈ S, d u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hScard : (0 : Real) < S.card := by exact_mod_cast hS.card_pos
  have hU : (U.card : Real) ≤ (S.card : Real)/4 := by
    have h := hlower.trans (hupper.trans (hsum.le.trans hB))
    nlinarith
  have hpartition : (T.card : Real) + U.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S) H
  refine ⟨T, Finset.filter_subset _ _, by linarith, ?_⟩
  intro u hu
  exact (Finset.mem_filter.mp hu).2

end LeanProofs.GowersSzemeredi
