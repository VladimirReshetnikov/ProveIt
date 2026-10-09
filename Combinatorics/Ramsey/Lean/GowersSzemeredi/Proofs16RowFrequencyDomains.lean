import GowersSzemeredi.Proofs16CoherentAnchorRowDomains
import GowersSzemeredi.Proofs16JointSelectionUniformControls

/-! Each projection of the retained quadruples is dense, and every map
chosen for that position is Freiman on the entire projection. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_row_frequency_domains {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N))
    (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N))
    {delta r kappa : Real} (hs : s.JointValid T delta d r)
    (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3) (hR : kappa*(N : Real)^3 ≤ R.card)
    (hdom : ∀ a ∈ R, ∀ j, ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) :
    ∀ j, kappa*N ≤ ((anchorRowSupport R j).card : Real) ∧
      ∀ i ∈ J j, (anchorRowSupport R j) ⊆ (s.maps.get i).domain ∧
        FreimanHom 2 (anchorRowSupport R j) (s.maps.get i).toFun := by
  intro j
  refine ⟨additive_quadruples_row_density R hadd hR j,?_⟩
  intro i hi
  have hsub : anchorRowSupport R j ⊆ (s.maps.get i).domain := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    exact hdom q hq j i hi
  have hf := PairFrequencyMap.JointControlled.uniform_bounds (s.maps.get i) (hs.1 _ (List.get_mem s.maps i))
  exact ⟨hsub,IsAddFreimanHom.subset hsub hf.2.2.2 (Set.mapsTo_univ _ _)⟩

theorem exact_row_frequencies_on_support {N : Nat} [NeZero N]
    (s : PairSelectionState N) (J : Fin 4 → Finset (Fin s.maps.length))
    (R : Finset (Fin 4 → ZMod N)) (x y : ZMod N → ZMod N)
    (hfreq : ∀ a ∈ R, ∀ j, commonIndexAnchorFrequencies s (J j) (a j) =
      shiftAnchorFrequencies s.frequencies x y (a j)) :
    ∀ j, ∀ a ∈ anchorRowSupport R j, commonIndexAnchorFrequencies s (J j) a =
      shiftAnchorFrequencies s.frequencies x y a := by
  intro j a ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
  exact hfreq q hq j

end LeanProofs.GowersSzemeredi
