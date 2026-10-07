import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

variable {J K I : Type*} [Fintype J] [Fintype K] [DecidableEq I]

theorem finiteRows_two_le_of_no_singletons (a : (J × K) → I)
    (h : ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1) (s : J × K) :
    2 ≤ (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card := by
  have hp : 0 < (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card := by
    apply Finset.card_pos.mpr
    exact ⟨s.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s.2, rfl⟩⟩⟩
  have hn := h (a s)
  omega

end Erdos3

end

end OAI
