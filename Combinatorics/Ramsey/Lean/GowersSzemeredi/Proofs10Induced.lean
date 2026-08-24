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

private lemma inducedTranslate_card {N : Nat}
    (A : Finset (ZMod N)) (d : ZMod N) :
    (section10Translate A d).card = A.card := by
  classical
  unfold section10Translate
  exact Finset.card_image_of_injective A (add_left_injective d)

private lemma inducedTranslate_mono {N : Nat}
    {A A' : Finset (ZMod N)} (hAA' : A ⊆ A') (d : ZMod N) :
    section10Translate A d ⊆ section10Translate A' d := by
  intro x hx
  rw [mem_inducedTranslate_iff] at hx ⊢
  exact hAA' hx

/-- Inclusion-exclusion inside a common finite ambient set. -/
private lemma inter_card_lower_of_subsets {X : Type*} [DecidableEq X]
    (S T U : Finset X) (hSU : S ⊆ U) (hTU : T ⊆ U) :
    (S.card : Real) + T.card - U.card ≤ (S ∩ T).card := by
  have hunion : S ∪ T ⊆ U := Finset.union_subset hSU hTU
  have hcardUnion : (S ∪ T).card ≤ U.card := Finset.card_le_card hunion
  have hcardIdentity := Finset.card_union_add_card_inter S T
  have hcardUnionReal : ((S ∪ T).card : Real) ≤ U.card := by
    exact_mod_cast hcardUnion
  have hcardIdentityReal :
      ((S ∪ T).card : Real) + (S ∩ T).card = S.card + T.card := by
    exact_mod_cast hcardIdentity
  linarith

private lemma induced_bohr_zero_mem {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hdelta : 0 ≤ delta) :
    (0 : ZMod N) ∈ bohr K delta := by
  classical
  unfold bohr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_zero,
    centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
  intro r hr
  positivity

/-- The `7/8` Bohr-overlap estimate at the radius used in Corollary 10.11. -/
private lemma induced_bohr_overlap {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) (hK : K.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    let k := K.card
    let B := bohr K delta
    let zeta := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
    let C := bohr K zeta
    ∀ d, d ∈ C →
      (7 / 8 : Real) * B.card ≤
        (B ∩ section10Translate B d).card := by
  classical
  dsimp only
  intro d hd
  let k : Nat := K.card
  let zeta : Real := (2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k
  have hk : 0 < k := Finset.card_pos.mpr hK
  have hkReal : (0 : Real) < k := by exact_mod_cast hk
  have hfactorNonneg : 0 ≤ (2 : Real) ^ (-((k : Real) + 4)) :=
    Real.rpow_nonneg (by norm_num) _
  have hfactorLeOne : (2 : Real) ^ (-((k : Real) + 4)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : Real) ≤ k + 4 := by positivity
      linarith)
  have hdeltaPowNonneg : 0 ≤ delta ^ k := pow_nonneg hdelta.le _
  have hdeltaPowLe : delta ^ k ≤ delta := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one hdelta.le hdeltaOne
        (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hzetaPos : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have hzetaLe : zeta ≤ delta := by
    calc
      zeta ≤ 1 * delta ^ k / k := by
        dsimp only [zeta]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactorLeOne hdeltaPowNonneg) hkReal.le
      _ ≤ delta ^ k := by
        simpa only [one_mul] using
          div_le_self hdeltaPowNonneg (by exact_mod_cast hk)
      _ ≤ delta := hdeltaPowLe
  have htwoCancel :
      (2 : Real) ^ (k + 1) * (2 : Real) ^ (-((k : Real) + 4)) = 1 / 8 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    rw [show ((k + 1 : Nat) : Real) + (-((k : Real) + 4)) = -3 by
      norm_num
      ring]
    norm_num [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  have hdeltaCancel : delta ^ (-(k : Real)) * delta ^ k = 1 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hdelta]
    norm_num
  have hcoeff :
      (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k * zeta = 1 / 8 := by
    dsimp only [zeta]
    calc
      (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k *
          ((2 : Real) ^ (-((k : Real) + 4)) * delta ^ k / k) =
          ((2 : Real) ^ (k + 1) * (2 : Real) ^ (-((k : Real) + 4))) *
            (delta ^ (-(k : Real)) * delta ^ k) := by
        field_simp [hkReal.ne']
      _ = 1 / 8 := by rw [htwoCancel, hdeltaCancel]; norm_num
  have hraw := lemma_10_10_holds N k K delta zeta rfl hdelta hdeltaOne
    hzetaPos.le hzetaLe d hd
  change (1 - (2 : Real) ^ (k + 1) * delta ^ (-(k : Real)) * k * zeta) *
      (bohr K delta).card ≤
        (bohr K delta ∩ section10Translate (bohr K delta) d).card at hraw
  rw [hcoeff] at hraw
  norm_num at hraw ⊢
  exact hraw

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
    exact ⟨0, induced_bohr_zero_mem K delta hdelta.le⟩
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
  have hthetaLe : theta ≤ (1 / 64 : Real) := by
    nlinarith
  have hthetaB : theta * (B.card : Real) ≤ (1 / 64 : Real) * B.card :=
    mul_le_mul_of_nonneg_right hthetaLe hBcardPos.le
  have hsqrtB' : Real.sqrt theta * (B'.card : Real) ≤
      (1 / 8 : Real) * B'.card :=
    mul_le_mul_of_nonneg_right hsqrt (by positivity)
  have hB'dense : (63 / 64 : Real) * B.card ≤ B'.card := by
    have hdense := hlocal.2.1
    nlinarith
  have hB'cardPos : (0 : Real) < B'.card := by
    nlinarith

  rw [section10RegularSet, Finset.mem_filter] at hw1 hw2
  let Good (w : X) (d : ZMod N) : Prop :=
    AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
      phi z - phi w = psi d
  let G1 : Finset (ZMod N) := B'.filter (Good w1)
  let G2 : Finset (ZMod N) := B'.filter (Good w2)
  have hw1W : w1 ∈ W := hw1.1
  have hw2W : w2 ∈ W := hw2.1
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
      induced_bohr_overlap K delta hK hdelta hdeltaOne c hc
  let T : Finset (ZMod N) := section10Translate B c
  let T' : Finset (ZMod N) := section10Translate B' c
  let U : Finset (ZMod N) := B ∩ T
  let U' : Finset (ZMod N) := B' ∩ T'
  have hT'sub : T' ⊆ T := inducedTranslate_mono hlocal.1 c
  have hU'sub : U' ⊆ U := by
    intro x hx
    change x ∈ B' ∩ T' at hx
    change x ∈ B ∩ T
    exact Finset.mem_inter.mpr
      ⟨hlocal.1 (Finset.mem_inter.mp hx).1,
        hT'sub (Finset.mem_inter.mp hx).2⟩
  let E0 : Finset (ZMod N) := B \ B'
  let Ec : Finset (ZMod N) := T \ T'
  have hE0 : (E0.card : Real) ≤ theta * B.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card hlocal.1
    have hpartReal : ((B \ B').card : Real) + B'.card = B.card := by
      exact_mod_cast hpartNat
    dsimp only [E0]
    nlinarith [hlocal.2.1]
  have hEc : (Ec.card : Real) ≤ theta * B.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card hT'sub
    have hpartReal : ((T \ T').card : Real) + T'.card = T.card := by
      exact_mod_cast hpartNat
    rw [show T.card = B.card by exact inducedTranslate_card B c,
      show T'.card = B'.card by exact inducedTranslate_card B' c] at hpartReal
    dsimp only [Ec]
    nlinarith [hlocal.2.1]
  have hdiffUsub : U \ U' ⊆ E0 ∪ Ec := by
    intro x hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxnot := (Finset.mem_sdiff.mp hx).2
    have hxB : x ∈ B := (Finset.mem_inter.mp hxU).1
    have hxT : x ∈ T := (Finset.mem_inter.mp hxU).2
    by_cases hxB' : x ∈ B'
    · have hxnotT' : x ∉ T' := by
        intro hxT'
        exact hxnot (Finset.mem_inter.mpr ⟨hxB', hxT'⟩)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxnotT'⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxB, hxB'⟩))
  have hdiffUNat : (U \ U').card ≤ E0.card + Ec.card := by
    exact (Finset.card_le_card hdiffUsub).trans (Finset.card_union_le E0 Ec)
  have hdiffU : ((U \ U').card : Real) ≤ 2 * theta * B.card := by
    have hdiffUReal : ((U \ U').card : Real) ≤ E0.card + Ec.card := by
      exact_mod_cast hdiffUNat
    nlinarith
  have hpartU : ((U \ U').card : Real) + U'.card = U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hU'sub
  have hU'lowerB : (27 / 32 : Real) * B.card ≤ U'.card := by
    change (7 / 8 : Real) * B.card ≤ U.card at hoverlap
    nlinarith
  have hU'lowerB' : (27 / 32 : Real) * B'.card ≤ U'.card := by
    have hscale := mul_le_mul_of_nonneg_left hB'cardLe
      (by norm_num : (0 : Real) ≤ 27 / 32)
    exact hscale.trans hU'lowerB

  let TG1 : Finset (ZMod N) := section10Translate G1 c
  let H : Finset (ZMod N) := (U' ∩ G2) ∩ TG1
  have hG1sub : G1 ⊆ B' := Finset.filter_subset _ _
  have hG2sub : G2 ⊆ B' := Finset.filter_subset _ _
  have hTG1sub : TG1 ⊆ T' := inducedTranslate_mono hG1sub c
  have hG1def : ((B' \ G1).card : Real) ≤
      Real.sqrt theta * B'.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card hG1sub
    have hpartReal : ((B' \ G1).card : Real) + G1.card = B'.card := by
      exact_mod_cast hpartNat
    nlinarith
  have hG2def : ((B' \ G2).card : Real) ≤
      Real.sqrt theta * B'.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card hG2sub
    have hpartReal : ((B' \ G2).card : Real) + G2.card = B'.card := by
      exact_mod_cast hpartNat
    nlinarith
  have hTG1def : ((T' \ TG1).card : Real) ≤
      Real.sqrt theta * B'.card := by
    have hpartNat := Finset.card_sdiff_add_card_eq_card hTG1sub
    have hpartReal : ((T' \ TG1).card : Real) + TG1.card = T'.card := by
      exact_mod_cast hpartNat
    rw [show T'.card = B'.card by exact inducedTranslate_card B' c,
      show TG1.card = G1.card by exact inducedTranslate_card G1 c] at hpartReal
    nlinarith
  have hHsub : H ⊆ U' := by
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
  have hdiffHsub : U' \ H ⊆ (B' \ G2) ∪ (T' \ TG1) := by
    intro x hx
    have hxU' := (Finset.mem_sdiff.mp hx).1
    have hxnot := (Finset.mem_sdiff.mp hx).2
    have hxB' : x ∈ B' := (Finset.mem_inter.mp hxU').1
    have hxT' : x ∈ T' := (Finset.mem_inter.mp hxU').2
    by_cases hxG2 : x ∈ G2
    · have hxnotTG1 : x ∉ TG1 := by
        intro hxTG1
        exact hxnot (Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨hxU', hxG2⟩, hxTG1⟩)
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hxT', hxnotTG1⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hxB', hxG2⟩))
  have hdiffHNat : (U' \ H).card ≤
      (B' \ G2).card + (T' \ TG1).card := by
    exact (Finset.card_le_card hdiffHsub).trans
      (Finset.card_union_le (B' \ G2) (T' \ TG1))
  have hdiffH : ((U' \ H).card : Real) ≤
      2 * Real.sqrt theta * B'.card := by
    have hdiffHReal : ((U' \ H).card : Real) ≤
        (B' \ G2).card + (T' \ TG1).card := by
      exact_mod_cast hdiffHNat
    nlinarith only [hdiffHReal, hG2def, hTG1def]
  have hpartH : ((U' \ H).card : Real) + H.card = U'.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hHsub
  have hHlower : (19 / 32 : Real) * B'.card ≤ H.card := by
    nlinarith only [hpartH, hU'lowerB', hdiffH, hsqrtB']
  have hHpos : 0 < H.card := by
    have hscaled : (0 : Real) < (19 / 32 : Real) * B'.card :=
      mul_pos (by norm_num) hB'cardPos
    exact_mod_cast (show (0 : Real) < H.card by
      nlinarith only [hscaled, hHlower])
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
  have hthetaF : theta * (F.card : Real) ≤ (1 / 64 : Real) * F.card :=
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
