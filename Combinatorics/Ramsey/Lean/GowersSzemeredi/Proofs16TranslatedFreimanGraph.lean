import GowersSzemeredi.Proofs16EscapingProgressionDifferenceMap

/-! Make the translated domain and constant term of a common Freiman
map explicit before adjoining its values to selected frequency families. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def translatedFreimanDomain {N : Nat} (S : Finset (ZMod N)) (a : ZMod N) : Finset (ZMod N) :=
  S.image fun x => a+x

theorem mem_translatedFreimanDomain {N : Nat} (S : Finset (ZMod N)) (a x : ZMod N) :
    x ∈ translatedFreimanDomain S a ↔ x-a ∈ S := by
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa only [add_sub_cancel_left] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x-a,hx,by ring⟩

theorem translatedFreimanDomain_card {N : Nat} (S : Finset (ZMod N)) (a : ZMod N) :
    (translatedFreimanDomain S a).card = S.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)

theorem freiman_translate_graph {N : Nat} (S : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (a c : ZMod N) (hpsi : FreimanHom 2 S psi) :
    FreimanHom 2 (translatedFreimanDomain S a) (fun x => c+psi (x-a)) := by
  apply isAddFreimanHom_two.mpr
  refine ⟨Set.mapsTo_univ _ _,?_⟩
  intro x hx y hy z hz w hw he
  have h := hpsi.add_eq_add ((mem_translatedFreimanDomain S a x).mp hx)
    ((mem_translatedFreimanDomain S a y).mp hy) ((mem_translatedFreimanDomain S a z).mp hz)
    ((mem_translatedFreimanDomain S a w).mp hw) (by linear_combination he)
  linear_combination h

end LeanProofs.GowersSzemeredi
