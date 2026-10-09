import GowersSzemeredi.Proofs16RowLabelSelection

/-! All four Freiman frequency families can be used at every point of
their common progression. Their union gives one row-independent domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def unifiedRowFrequencies {N m : Nat} (J : Fin 4 → Finset (Fin m))
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (x : ZMod N) : Finset (ZMod N) :=
  Finset.univ.biUnion (fun j : Fin 4 => varyingRowFrequencies J psi j x)

def unifiedRowBohrDomain {N m : Nat} [NeZero N] (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) (psi : Fin 4 → Fin m → ZMod N → ZMod N)
    (sigma : Real) (x : ZMod N) : Finset (ZMod N) :=
  bohr (affineRowConstants J c ∪ unifiedRowFrequencies J psi x) (sigma/2)

theorem unifiedRowFrequencies_card_le {N m K : Nat} (J : Fin 4 → Finset (Fin m))
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (hJ : ∀ j, (J j).card ≤ K) (x : ZMod N) :
    (unifiedRowFrequencies J psi x).card ≤ 4*K := by
  calc _ ≤ ∑ j : Fin 4, (varyingRowFrequencies J psi j x).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, K := Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (hJ j)
    _ = _ := by simp

theorem unifiedRowSpectrum_card_le {N m K : Nat} (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) (psi : Fin 4 → Fin m → ZMod N → ZMod N)
    (hJ : ∀ j, (J j).card ≤ K) (x : ZMod N) :
    (affineRowConstants J c ∪ unifiedRowFrequencies J psi x).card ≤ 8*K := by
  exact (Finset.card_union_le _ _).trans
    (by have hc := affineRowConstants_card_le J c hJ
        have hv := unifiedRowFrequencies_card_le J psi hJ x
        omega)

theorem unifiedRowBohrDomain_subset {N m : Nat} [NeZero N]
    (J : Fin 4 → Finset (Fin m)) (c : Fin 4 → Fin m → ZMod N)
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (sigma : Real) (j : Fin 4) (x : ZMod N) :
    unifiedRowBohrDomain J c psi sigma x ⊆ affineRowBohrDomain J c psi sigma j x := by
  intro z hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  intro v hv
  apply (Finset.mem_filter.mp hz).2
  rcases Finset.mem_union.mp hv with hc | hv
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩)

/-- The varying spectrum is the image of one fixed finite index type. -/
theorem unifiedRowFrequencies_eq_image {N m : Nat} (J : Fin 4 → Finset (Fin m))
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (x : ZMod N) :
    unifiedRowFrequencies J psi x =
      Finset.univ.image (fun i : (j : Fin 4) × {i // i ∈ J j} => psi i.1 i.2.val x) := by
  ext v
  simp only [unifiedRowFrequencies,varyingRowFrequencies,Finset.mem_biUnion,Finset.mem_univ,
    true_and,Finset.mem_image]
  constructor
  · rintro ⟨j,i,hi,he⟩
    exact ⟨⟨j,⟨i,hi⟩⟩,he⟩
  · rintro ⟨⟨j,i,hi⟩,he⟩
    exact ⟨j,i,hi,he⟩

end LeanProofs.GowersSzemeredi
