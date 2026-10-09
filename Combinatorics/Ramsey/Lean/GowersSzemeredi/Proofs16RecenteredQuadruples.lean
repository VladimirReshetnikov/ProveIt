import GowersSzemeredi.Proofs16AdditiveProgressionAveraging

/-! Recenter an entire quadruple family by one additive translation.
Cardinality and the original configuration membership are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def recenteredQuadruples {N : Nat} (R : Finset (Fin 4 → ZMod N))
    (t : Fin 4 → ZMod N) : Finset (Fin 4 → ZMod N) := R.image (fun a j => a j-t j)

theorem recenteredQuadruples_card {N : Nat} (R : Finset (Fin 4 → ZMod N))
    (t : Fin 4 → ZMod N) : (recenteredQuadruples R t).card = R.card := by
  apply Finset.card_image_of_injective
  intro a b h
  funext j
  simpa using congrFun h j

theorem mem_recenteredQuadruples {N : Nat} (R : Finset (Fin 4 → ZMod N))
    (t b : Fin 4 → ZMod N) : b ∈ recenteredQuadruples R t ↔ (fun j => t j+b j) ∈ R := by
  constructor
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    have he : (fun j => t j+(a j-t j)) = a := by funext j; ring
    simpa only [he] using ha
  · intro hb
    exact Finset.mem_image.mpr ⟨fun j => t j+b j,hb,by funext j; simp⟩

theorem recentered_localized_quadruples {N : Nat} (Q : Finset (Fin 4 → ZMod N))
    (P : Finset (ZMod N)) (t : Fin 4 → ZMod N)
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) (ht : t 0+t 1 = t 2+t 3) :
    ∀ b ∈ recenteredQuadruples (localizedQuadruples Q P t) t,
      b 0+b 1 = b 2+b 3 ∧ (∀ j, b j ∈ P) ∧ (fun j => t j+b j) ∈ Q := by
  intro b hb
  obtain ⟨hq,hP⟩ := Finset.mem_filter.mp ((mem_recenteredQuadruples _ t b).mp hb)
  have hadd := hQ _ hq
  refine ⟨?_,?_,hq⟩
  · linear_combination hadd-ht
  · intro j
    simpa only [add_sub_cancel_left] using hP j

end LeanProofs.GowersSzemeredi
