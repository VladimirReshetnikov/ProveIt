import GowersSzemeredi.Proofs16FiniteCoverPatternSelection

/-! Refine whole quadruples simultaneously through the coordinate-cell
covers of their exact row frequency maps. Every selected map becomes
order eight on its row support, with a controlled finite loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem joint_rows_freiman_eight {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N))
    (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N))
    {delta r : Real} (hs : s.JointValid T delta d r)
    (hJ : ∀ j, (J j).card ≤ 2*jointSelectionRank d r) (hR : R.Nonempty)
    (hdom : ∀ a ∈ R, ∀ j, ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) :
    ∃ R' : Finset (Fin 4 → ZMod N), R' ⊆ R ∧ R'.Nonempty ∧
      R.card ≤ 16^(8*jointSelectionRank d r*jointMapRank delta d r)*R'.card ∧
      ∀ j, ∀ i ∈ J j, FreimanHom 8 (anchorRowSupport R' j) (s.maps.get i).toFun := by
  let I := (j : Fin 4) × ↥(J j)
  let C : I → Finset (Finset (ZMod N)) := fun z => (s.maps.get z.2).eightCover
  have hcontrols (z : I) := PairFrequencyMap.joint_eightCover (s.maps.get z.2)
    (hs.1 _ (List.get_mem s.maps z.2))
  have hcover : ∀ a ∈ R, ∀ z : I, ∃ D ∈ C z, a z.1 ∈ D := by
    intro a ha z
    have h := hdom a ha z.1 z.2 z.2.property
    rw [← (hcontrols z).2.2.1] at h
    simpa only [Finset.mem_biUnion,id_eq,C] using h
  obtain ⟨D,R',hDC,hsub,hcount,hR',hmem⟩ := exists_dense_cover_pattern R C (fun a z => a z.1)
    hR (fun z => (hcontrols z).1) (fun z => (hcontrols z).2.1) hcover
  have hcardI : Fintype.card I ≤ 8*jointSelectionRank d r := by
    change Fintype.card ((j : Fin 4) × ↥(J j)) ≤ _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc ∑ j : Fin 4, (J j).card ≤ ∑ _j : Fin 4, 2*jointSelectionRank d r :=
        Finset.sum_le_sum fun j _ => hJ j
      _ = _ := by simp; omega
  have hp : (16^jointMapRank delta d r)^Fintype.card I ≤
      16^(8*jointSelectionRank d r*jointMapRank delta d r) := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (jointMapRank delta d r) hcardI
  refine ⟨R',hsub,hR',hcount.trans (Nat.mul_le_mul_right R'.card hp),?_⟩
  intro j i hi
  let z : I := ⟨j,⟨i,hi⟩⟩
  have hfreq := ((hcontrols z).2.2.2 (D z) (hDC z)).2
  have hsupport : anchorRowSupport R' j ⊆ D z := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    exact hmem q hq z
  exact IsAddFreimanHom.subset hsupport hfreq (Set.mapsTo_univ _ _)

def rowEightDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  kappa/(16 : Real)^(8*jointSelectionRank d r*jointMapRank delta d r)

theorem rowEightDensity_pos {delta kappa r : Real} {d : Nat} (hk : 0 < kappa) :
    0 < rowEightDensity delta kappa d r := by unfold rowEightDensity; positivity

theorem joint_rows_eight_density {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N))
    (J : Fin 4 → Finset (Fin s.maps.length)) (R : Finset (Fin 4 → ZMod N))
    {delta r kappa : Real} (hs : s.JointValid T delta d r)
    (hJ : ∀ j, (J j).card ≤ 2*jointSelectionRank d r) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ R.card)
    (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3)
    (hdom : ∀ a ∈ R, ∀ j, ∀ i ∈ J j, a j ∈ (s.maps.get i).domain) :
    ∃ R' : Finset (Fin 4 → ZMod N), R' ⊆ R ∧
      rowEightDensity delta kappa d r*(N : Real)^3 ≤ R'.card ∧
      ∀ j, rowEightDensity delta kappa d r*N ≤ ((anchorRowSupport R' j).card : Real) ∧
        ∀ i ∈ J j, FreimanHom 8 (anchorRowSupport R' j) (s.maps.get i).toFun := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hk (pow_pos hn 3)).trans_le hmass
  obtain ⟨R',hsub,_,hcount,hfreq⟩ := joint_rows_freiman_eight s T J R hs hJ hR hdom
  have hc : (R.card : Real) ≤ (16 : Real)^(8*jointSelectionRank d r*jointMapRank delta d r)*(R'.card : Real) := by
    exact_mod_cast hcount
  have hm : rowEightDensity delta kappa d r*(N : Real)^3 ≤ R'.card := by
    unfold rowEightDensity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hmass.trans hc
  exact ⟨R',hsub,hm,fun j => ⟨additive_quadruples_row_density R' (fun a ha => hadd a (hsub ha)) hm j,hfreq j⟩⟩

end LeanProofs.GowersSzemeredi
