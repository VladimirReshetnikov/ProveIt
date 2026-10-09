import GowersSzemeredi.Proofs16ProgressionCellLinearity
import Mathlib.Data.Multiset.Fintype

/-! Convert a finite-tuple sum-preservation proof to the standard
multiset definition of a Freiman homomorphism. Repetitions are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem freimanHom_of_fin_sums {N k : Nat} (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (h : ∀ u v : Fin k → ZMod N, (∀ j, u j ∈ A) → (∀ j, v j ∈ A) →
      (∑ j, u j) = ∑ j, v j → (∑ j, f (u j)) = ∑ j, f (v j)) : FreimanHom k A f := by
  refine ⟨Set.mapsTo_univ _ _,?_⟩
  intro s t hsA htA hs ht he
  let es : s ≃ Fin k := Fintype.equivFinOfCardEq (by simpa only [Multiset.card_coe] using hs)
  let et : t ≃ Fin k := Fintype.equivFinOfCardEq (by simpa only [Multiset.card_coe] using ht)
  let u : Fin k → ZMod N := fun j => (es.symm j : ZMod N)
  let v : Fin k → ZMod N := fun j => (et.symm j : ZMod N)
  have hsumS (g : ZMod N → ZMod N) : (∑ j, g (u j)) = (s.map g).sum := by
    calc _ = ∑ x : s, g (x : ZMod N) := es.symm.sum_comp _
      _ = _ := congrArg Multiset.sum (Multiset.map_univ s g)
  have hsumT (g : ZMod N → ZMod N) : (∑ j, g (v j)) = (t.map g).sum := by
    calc _ = ∑ x : t, g (x : ZMod N) := et.symm.sum_comp _
      _ = _ := congrArg Multiset.sum (Multiset.map_univ t g)
  have hsum : (∑ j, u j) = ∑ j, v j := by
    have hs' := hsumS id
    have ht' := hsumT id
    simp only [Multiset.map_id] at hs' ht'
    exact hs'.trans (he.trans ht'.symm)
  have hf := h u v (fun j => hsA (Multiset.coe_mem (x := es.symm j)))
    (fun j => htA (Multiset.coe_mem (x := et.symm j))) hsum
  rw [hsumS f,hsumT f] at hf
  exact hf

end LeanProofs.GowersSzemeredi
