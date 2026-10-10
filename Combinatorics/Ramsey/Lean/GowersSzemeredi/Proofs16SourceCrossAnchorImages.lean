import GowersSzemeredi.Proofs16DifferenceProgressionMaps
import GowersSzemeredi.Proofs16QuerySourceAgreement

/-! Compare a chosen difference map with the difference at any other
valid anchor. Repeated padding columns add no frequency outside its
existing endpoint domain; reference-map values cancel but spectra remain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sourceCrossAnchorTuple {N : Nat} (v : ZMod N → ZMod N) (a u : ZMod N) : PairedColumnTuple N :=
  ![(v a+a,v a),(u,u+a),(v a,v a),(v a,v a)]

theorem source_cross_anchor_index {N : Nat} (v : ZMod N → ZMod N) (a u : ZMod N) :
    pairedColumnIndex (sourceCrossAnchorTuple v a u) = 0 := by
  rw [pairedColumnIndex,Fin.sum_univ_four]
  change ((v a+a)-v a)+(u-(u+a))+(v a-v a)+(v a-v a)=0
  ring

theorem source_cross_anchor_defect {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (v : ZMod N → ZMod N) (a u y : ZMod N) :
    pairedColumnDefect (normalizedRepresentationMap L f) (sourceCrossAnchorTuple v a u) y =
      differenceAnchorMap (normalizedRepresentationMap L f) v a y-
        representationColumnMap L (f (u+a)) y+representationColumnMap L (f u) y := by
  rw [pairedColumnDefect,Fin.sum_univ_four]
  change ((normalizedRepresentationMap L f (v a+a) y-normalizedRepresentationMap L f (v a) y)+
    (normalizedRepresentationMap L f u y-normalizedRepresentationMap L f (u+a) y)+
    (normalizedRepresentationMap L f (v a) y-normalizedRepresentationMap L f (v a) y)+
    (normalizedRepresentationMap L f (v a) y-normalizedRepresentationMap L f (v a) y)) = _
  dsimp only [normalizedRepresentationMap,differenceAnchorMap]
  ring

theorem source_cross_anchor_domain_subset {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (v : ZMod N → ZMod N) (a u : ZMod N) (rho : Real) :
    bohr (differenceAnchorSpectrum T v a ∪ (T u ∪ T (u+a))) rho ⊆
      bohr (pairedColumnSpectrum T (sourceCrossAnchorTuple v a u)) rho := by
  intro y hy
  rw [bohr_union] at hy
  obtain ⟨hpsi,haux⟩ := Finset.mem_inter.mp hy
  rw [differenceAnchorSpectrum,bohr_union] at hpsi
  rw [bohr_union] at haux
  obtain ⟨hva',hva⟩ := Finset.mem_inter.mp hpsi
  obtain ⟨hu,hua⟩ := Finset.mem_inter.mp haux
  apply (mem_paired_column_spectrum_bohr T _ rho y).mpr
  intro i
  fin_cases i
  · exact ⟨hva',hva⟩
  · exact ⟨hu,hua⟩
  · exact ⟨hva,hva⟩
  · exact ⟨hva,hva⟩

/-- All tiny-core eight-tuples compare the chosen map with every other
anchor difference on the actual common domain. -/
theorem source_cross_anchor_image {N J : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N)
    (v : ZMod N → ZMod N) (rho : Real) (a u : ZMod N)
    (hva : v a ∈ C) (hva' : v a+a ∈ C) (hu : u ∈ C) (hua : u+a ∈ C)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q=0 →
      PairedColumnImageRelation (normalizedRepresentationSpectrum T f) (normalizedRepresentationMap L f) rho J q) :
    ((bohr (differenceAnchorSpectrum (normalizedRepresentationSpectrum T f) v a ∪
      (normalizedRepresentationSpectrum T f u ∪ normalizedRepresentationSpectrum T f (u+a))) rho).image
      (fun y => differenceAnchorMap (normalizedRepresentationMap L f) v a y-
        representationColumnMap L (f (u+a)) y+representationColumnMap L (f u) y)).card ≤ J := by
  have hq : ∀ i, (sourceCrossAnchorTuple v a u i).1 ∈ C ∧ (sourceCrossAnchorTuple v a u i).2 ∈ C := by
    intro i
    fin_cases i
    · exact ⟨hva',hva⟩
    · exact ⟨hu,hua⟩
    · exact ⟨hva,hva⟩
    · exact ⟨hva,hva⟩
  have hsrc := h8 _ hq (source_cross_anchor_index v a u)
  apply (image_card_le_of_eq_on_subset _ _ _ _
    (source_cross_anchor_domain_subset (normalizedRepresentationSpectrum T f) v a u rho) ?_).trans hsrc
  intro y _
  exact (source_cross_anchor_defect L f v a u y).symm

end LeanProofs.GowersSzemeredi
