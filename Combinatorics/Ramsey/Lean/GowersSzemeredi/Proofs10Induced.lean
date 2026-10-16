import GowersSzemeredi.Proofs10Bohr

/-!
# The induced-difference assertion in Lemma 10.12

This file proves the final intersection argument that identifies differences
of `phi` on the regular set with the homomorphism induced on the smaller Bohr
neighborhood.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma mem_inducedTranslate_iff {N : Nat}
    (A : Finset (ZMod N)) (d x : ZMod N) :
    x ∈ section10Translate A d ↔ x - d ∈ A := by
  classical
  unfold section10Translate
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    subst x
    simpa using hy
  · intro hx
    refine Finset.mem_image.mpr ⟨x - d, hx, ?_⟩
    abel

theorem lemma_10_12_holds : lemma_10_12 := by
  classical
  intro N _ X _ _ D phi K delta theta W B' psi psi1
    hK hdelta hdeltaOne hsqrt hfibre
  dsimp only
  intro hlocal hpsi1 hinduced w1 hw1 w2 hw2 hc
  let k : Nat := K.card
  let B : Finset (ZMod N) := bohr K delta
  let zeta : Real := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
  let C : Finset (ZMod N) := bohr K zeta
  let c : ZMod N := D.index w1 - D.index w2
  change IsSection10LocalDifferenceModel D phi W B B' psi theta at hlocal
  change FreimanHom 2 C psi1 at hpsi1
  change InducesDifferenceMap B' C psi psi1 at hinduced
  change c ∈ C at hc
  change phi w1 - phi w2 = psi1 c

  have hBne : B.Nonempty := by
    exact ⟨0, bohr_zero_mem K delta hdelta.le⟩
  have hBcardPos : (0 : Real) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hBne
  have hB'cardLeNat : B'.card ≤ B.card :=
    Finset.card_le_card hlocal.1
  have hB'cardLe : (B'.card : Real) ≤ B.card := by
    exact_mod_cast hB'cardLeNat
  have hthetaNonneg : 0 ≤ theta := by
    have hdense := hlocal.2.1
    nlinarith
  have hsqrtNonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt theta) ^ 2 = theta :=
    Real.sq_sqrt hthetaNonneg
  have hthetaLe : theta ≤ (1 / 8 : Real) := by
    nlinarith
  have hthetaB : theta * (B.card : Real) ≤ (1 / 8 : Real) * B.card :=
    mul_le_mul_of_nonneg_right hthetaLe hBcardPos.le
  have hB'dense : (7 / 8 : Real) * B.card ≤ B'.card := by
    have hdense := hlocal.2.1
    nlinarith
  have hB'cardPos : (0 : Real) < B'.card := by
    nlinarith
  have hsqrtB' : Real.sqrt theta * (B'.card : Real) <
      (5 / 16 : Real) * B'.card :=
    mul_lt_mul_of_pos_right hsqrt hB'cardPos

  rw [section10RegularSet, Finset.mem_filter] at hw1 hw2
  let Good (w : X) (d : ZMod N) : Prop :=
    AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
      phi z - phi w = psi d
  let G1 : Finset (ZMod N) := B'.filter (Good w1)
  let G2 : Finset (ZMod N) := B'.filter (Good w2)
  have hw1W : w1 ∈ W := hw1.1
  have hw1Good : AlmostEvery (1 - Real.sqrt theta) B' (Good w1) := by
    simpa only [Good] using hw1.2
  have hw2Good : AlmostEvery (1 - Real.sqrt theta) B' (Good w2) := by
    simpa only [Good] using hw2.2
  have hG1 : (1 - Real.sqrt theta) * (B'.card : Real) ≤ G1.card := by
    simpa only [AlmostEvery, G1] using hw1Good
  have hG2 : (1 - Real.sqrt theta) * (B'.card : Real) ≤ G2.card := by
    simpa only [AlmostEvery, G2] using hw2Good

  have hoverlap : (7 / 8 : Real) * B.card ≤
      (B ∩ section10Translate B c).card := by
    simpa only [k, B, zeta, C] using
      corollary_10_11_overlap K delta hK hdelta hdeltaOne c hc
  let T : Finset (ZMod N) := section10Translate B c
  let T' : Finset (ZMod N) := section10Translate B' c
  let U : Finset (ZMod N) := B ∩ T
  let U' : Finset (ZMod N) := B' ∩ T'
  have hT'sub : T' ⊆ T := section10Translate_mono hlocal.1 c
  have hU'lowerB : (5 / 8 : Real) * B.card ≤ U'.card := by
    have hinter := inter_card_lower_of_subsets B' T' (B ∪ T)
      (hlocal.1.trans Finset.subset_union_left)
      (hT'sub.trans Finset.subset_union_right)
    have hunion : ((B ∪ T).card : Real) + U.card = B.card + T.card := by
      exact_mod_cast Finset.card_union_add_card_inter B T
    have hTcard : T.card = B.card := section10Translate_card B c
    have hT'card : T'.card = B'.card := section10Translate_card B' c
    change (B'.card : Real) + T'.card - (B ∪ T).card ≤ U'.card at hinter
    change (7 / 8 : Real) * B.card ≤ U.card at hoverlap
    rw [hTcard] at hunion
    rw [hT'card] at hinter
    nlinarith only [hinter, hunion, hoverlap, hB'dense]
  have hU'lowerB' : (5 / 8 : Real) * B'.card ≤ U'.card := by
    have hscale := mul_le_mul_of_nonneg_left hB'cardLe
      (by norm_num : (0 : Real) ≤ 5 / 8)
    exact hscale.trans hU'lowerB

  let TG1 : Finset (ZMod N) := section10Translate G1 c
  let H : Finset (ZMod N) := (U' ∩ G2) ∩ TG1
  have hG1sub : G1 ⊆ B' := Finset.filter_subset _ _
  have hG2sub : G2 ⊆ B' := Finset.filter_subset _ _
  have hTG1sub : TG1 ⊆ T' := section10Translate_mono hG1sub c
  have hHposReal : (0 : Real) < H.card := by
    have hinterG2 := inter_card_lower_of_subsets U' G2 B'
      Finset.inter_subset_left hG2sub
    have hinterTG1 := inter_card_lower_of_subsets (U' ∩ G2) TG1 T'
      (Finset.inter_subset_left.trans Finset.inter_subset_right) hTG1sub
    have hTG1card : TG1.card = G1.card := section10Translate_card G1 c
    have hT'card : T'.card = B'.card := section10Translate_card B' c
    change ((U' ∩ G2).card : Real) + TG1.card - T'.card ≤ H.card at hinterTG1
    rw [hTG1card, hT'card] at hinterTG1
    nlinarith only [hinterG2, hinterTG1, hU'lowerB', hG1, hG2, hsqrtB']
  have hHpos : 0 < H.card := by
    exact_mod_cast hHposReal
  obtain ⟨x, hxH⟩ := Finset.card_pos.mp hHpos
  have hxU' : x ∈ U' := (Finset.mem_inter.mp (Finset.mem_inter.mp hxH).1).1
  have hxG2 : x ∈ G2 := (Finset.mem_inter.mp (Finset.mem_inter.mp hxH).1).2
  have hxTG1 : x ∈ TG1 := (Finset.mem_inter.mp hxH).2
  have hxB' : x ∈ B' := (Finset.mem_inter.mp hxU').1
  have hdB' : x - c ∈ B' :=
    (mem_inducedTranslate_iff B' c x).mp (Finset.mem_inter.mp hxU').2
  have hdG1 : x - c ∈ G1 :=
    (mem_inducedTranslate_iff G1 c x).mp hxTG1
  have hGood1 : Good w1 (x - c) := (Finset.mem_filter.mp hdG1).2
  have hGood2 : Good w2 x := (Finset.mem_filter.mp hxG2).2

  have hindex : D.index w1 + (x - c) = D.index w2 + x := by
    dsimp only [c]
    abel
  have hFne : (D.fibre (D.index w1 + (x - c))).Nonempty :=
    hfibre w1 hw1W (x - c) hdB'
  change AlmostEvery (1 - theta) (D.fibre (D.index w1 + (x - c)))
    (fun z => phi z - phi w1 = psi (x - c)) at hGood1
  change AlmostEvery (1 - theta) (D.fibre (D.index w2 + x))
    (fun z => phi z - phi w2 = psi x) at hGood2
  rw [← hindex] at hGood2
  let F : Finset X := D.fibre (D.index w1 + (x - c))
  let S : Finset X := F.filter fun z => phi z - phi w1 = psi (x - c)
  let Tz : Finset X := F.filter fun z => phi z - phi w2 = psi x
  have hS : (1 - theta) * (F.card : Real) ≤ S.card := by
    unfold AlmostEvery at hGood1
    rw [Finset.filter_congr_decidable] at hGood1
    simpa only [F, S] using hGood1
  have hTz : (1 - theta) * (F.card : Real) ≤ Tz.card := by
    unfold AlmostEvery at hGood2
    rw [Finset.filter_congr_decidable] at hGood2
    simpa only [F, Tz] using hGood2
  have hFcardPos : (0 : Real) < F.card := by
    exact_mod_cast Finset.card_pos.mpr hFne
  have hthetaF : theta * (F.card : Real) ≤ (1 / 8 : Real) * F.card :=
    mul_le_mul_of_nonneg_right hthetaLe hFcardPos.le
  have hinter := inter_card_lower_of_subsets S Tz F
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hSTposReal : (0 : Real) < (S ∩ Tz).card := by
    nlinarith only [hS, hTz, hinter, hFcardPos, hthetaF]
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by exact_mod_cast hSTposReal)
  have hzS : z ∈ S := (Finset.mem_inter.mp hz).1
  have hzT : z ∈ Tz := (Finset.mem_inter.mp hz).2
  have heq1 : phi z - phi w1 = psi (x - c) :=
    (Finset.mem_filter.mp hzS).2
  have heq2 : phi z - phi w2 = psi x :=
    (Finset.mem_filter.mp hzT).2
  have hmap : psi x - psi (x - c) = psi1 c :=
    hinduced c hc x hxB' (x - c) hdB' (by abel)
  calc
    phi w1 - phi w2 = (phi z - phi w2) - (phi z - phi w1) := by abel
    _ = psi x - psi (x - c) := by rw [heq2, heq1]
    _ = psi1 c := hmap

end LeanProofs.GowersSzemeredi
