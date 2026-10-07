import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem exists_sorted_positive_weights {d : ℕ} (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧ Monotone (w ∘ e) ∧
      ∀ i, i.val < a ↔ w (e i) = 1 := by
  classical
  let e := Tuple.sort w
  let a := (Finset.univ.filter (fun i => w (e i) ≤ 1)).card
  have hm : Monotone (w ∘ e) := Tuple.monotone_sort w
  refine ⟨e, a, ?_, hm, ?_⟩
  · exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin d)
  · intro i
    have hi : i.val < a ↔ w (e i) ≤ 1 :=
      Tuple.lt_card_le_iff_apply_le_of_monotone hm
    exact hi.trans ⟨fun h => Nat.le_antisymm h (hw (e i)), fun h => h.le⟩

end Erdos3

end

end OAI
