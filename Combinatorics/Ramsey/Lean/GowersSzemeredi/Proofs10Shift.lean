import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure

/-!
# Shifting almost-everywhere properties in Section 10

This file develops the double-counting shift lemma (Lemma 10.8, whose assembled
form `lemma_10_8_holds` is in `Proofs10ShiftSide`) used to construct the local
Freiman homomorphism.  The proof uses the fibre saturation and symmetry
hypotheses recorded in `IsSection10ShiftRegular`.

`fibreSize_eq_of_index_eq` and `lemma_10_8_holds` are in `Proofs10ShiftSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma mem_fibre_iff {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (s : ZMod N) (x : X) : x ∈ D.fibre s ↔ D.index x = s := by
  simp [MultifunctionDomain.fibre]

private lemma fibre_subset_of_saturated {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {W : Finset X} (hW : D.FibreSaturated W) {x : X} (hx : x ∈ W) :
    D.fibre (D.index x) ⊆ W := by
  intro y hy
  exact hW x hx y (mem_fibre_iff D _ _ |>.mp hy)

private lemma mem_shift_iff {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (x : X) :
    x ∈ D.shift W d ↔ ∃ w ∈ W, D.index x = D.index w + d := by
  simp [MultifunctionDomain.shift]

/-- If `w` lies in `W ∩ (W-d)`, its whole `d`-shifted fibre lies in `W`. -/
private lemma shifted_fibre_subset {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {W : Finset X} (hW : D.FibreSaturated W) (d : ZMod N) {w : X}
    (hw : w ∈ W ∩ D.shift W (-d)) :
    D.fibre (D.index w + d) ⊆ W := by
  obtain ⟨u, huW, hwu⟩ := (mem_shift_iff D W (-d) w).mp (Finset.mem_inter.mp hw).2
  have hi : D.index u = D.index w + d := by
    calc
      D.index u = (D.index u + -d) + d := by abel
      _ = D.index w + d := by rw [← hwu]
  rw [← hi]
  exact fibre_subset_of_saturated D hW huW

/-- The shifted fibre over an eligible point has a representative in `W`. -/
private lemma exists_shifted_representative {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {W : Finset X} (d : ZMod N) {w : X}
    (hw : w ∈ W ∩ D.shift W (-d)) :
    ∃ u ∈ W, D.index u = D.index w + d := by
  obtain ⟨u, huW, hwu⟩ := (mem_shift_iff D W (-d) w).mp (Finset.mem_inter.mp hw).2
  refine ⟨u, huW, ?_⟩
  calc
    D.index u = (D.index u + -d) + d := by abel
    _ = D.index w + d := by rw [← hwu]

/-! ### Elementary almost-everywhere cardinal arithmetic -/

private lemma almostEvery_bad_card_le {X : Type*} [DecidableEq X]
    (theta : Real) (U : Finset X) (P : X → Prop) [DecidablePred P]
    (hP : AlmostEvery (1 - theta) U P) :
    ((U.filter fun x => ¬ P x).card : Real) ≤ theta * U.card := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) + ((U.filter fun x => ¬ P x).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  nlinarith

private lemma bad_card_lt_of_not_almostEvery {X : Type*} [DecidableEq X]
    (tau : Real) (U : Finset X) (P : X → Prop) [DecidablePred P]
    (hP : ¬ AlmostEvery (1 - tau) U P) :
    tau * U.card < ((U.filter fun x => ¬ P x).card : Real) := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) + ((U.filter fun x => ¬ P x).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  push Not at hP
  nlinarith

private lemma almostEvery_of_bad_card_le {X : Type*} [DecidableEq X]
    (theta : Real) (U : Finset X) (P : X → Prop) [DecidablePred P]
    (hbad : ((U.filter fun x => ¬ P x).card : Real) ≤ theta * U.card) :
    AlmostEvery (1 - theta) U P := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) + ((U.filter fun x => ¬ P x).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable]
  nlinarith

lemma almostEvery_mono {X : Type*} [DecidableEq X]
    (p : Real) (U : Finset X) (P Q : X → Prop)
    (hP : AlmostEvery p U P) (hPQ : ∀ x, x ∈ U → P x → Q x) :
    AlmostEvery p U Q := by
  classical
  unfold AlmostEvery at hP ⊢
  rw [Finset.filter_congr_decidable] at hP ⊢
  exact hP.trans (by
    exact_mod_cast Finset.card_le_card (fun x hx =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        hPQ x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2⟩))

private lemma almostEvery_weaken_error {X : Type*} [DecidableEq X]
    (a b : Real) (U : Finset X) (P : X → Prop) (hab : a ≤ b)
    (hP : AlmostEvery (1 - a) U P) : AlmostEvery (1 - b) U P := by
  classical
  unfold AlmostEvery at hP ⊢
  rw [Finset.filter_congr_decidable] at hP ⊢
  nlinarith

private lemma almostEvery_and {X : Type*} [DecidableEq X]
    (a b : Real) (U : Finset X) (P Q : X → Prop)
    (hP : AlmostEvery (1 - a) U P) (hQ : AlmostEvery (1 - b) U Q) :
    AlmostEvery (1 - (a + b)) U (fun x => P x ∧ Q x) := by
  classical
  have hbadP := almostEvery_bad_card_le a U P hP
  have hbadQ := almostEvery_bad_card_le b U Q hQ
  have hsub : (U.filter fun x => ¬ (P x ∧ Q x)) ⊆
      (U.filter fun x => ¬ P x) ∪ (U.filter fun x => ¬ Q x) := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hx' := Finset.mem_filter.mp hx
    by_cases hPx : P x
    · exact Or.inr ⟨hx'.1, fun hQx => hx'.2 ⟨hPx, hQx⟩⟩
    · exact Or.inl ⟨hx'.1, hPx⟩
  have hbadNat :
      (U.filter fun x => ¬ (P x ∧ Q x)).card ≤
        (U.filter fun x => ¬ P x).card + (U.filter fun x => ¬ Q x).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hbad :
      ((U.filter fun x => ¬ (P x ∧ Q x)).card : Real) ≤ (a + b) * U.card := by
    have hbadReal :
        ((U.filter fun x => ¬ (P x ∧ Q x)).card : Real) ≤
          (U.filter fun x => ¬ P x).card + (U.filter fun x => ¬ Q x).card := by
      exact_mod_cast hbadNat
    nlinarith
  exact almostEvery_of_bad_card_le (a + b) U (fun x => P x ∧ Q x) hbad

private lemma exists_and_of_almostEvery {X : Type*} [DecidableEq X]
    (a b : Real) (U : Finset X) (P Q : X → Prop) (hU : U.Nonempty)
    (hab : a + b < 1) (hP : AlmostEvery (1 - a) U P)
    (hQ : AlmostEvery (1 - b) U Q) : ∃ x ∈ U, P x ∧ Q x := by
  classical
  have hAnd := almostEvery_and a b U P Q hP hQ
  unfold AlmostEvery at hAnd
  rw [Finset.filter_congr_decidable] at hAnd
  have hUcard : (0 : Real) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
  have hgood : (0 : Real) < ((U.filter fun x => P x ∧ Q x).card : Real) :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr hab) hUcard) hAnd
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hgood)
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-! ### The bad-pair double count -/

private def shiftBadPairs {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (P : X → Prop) : Finset (X × X) := by
  classical
  exact (W.product W).filter fun p =>
    D.index p.2 - D.index p.1 = d ∧ ¬ P p.2

private def shiftedBadCount {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (d : ZMod N) (P : X → Prop) (w : X) : Nat := by
  classical
  exact ((D.fibre (D.index w + d)).filter fun z => ¬ P z).card

private lemma shiftBadPairs_card_first {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (P : X → Prop) [DecidablePred P] :
    (shiftBadPairs D W d P).card =
      ∑ w ∈ W, (W.filter fun z =>
        D.index z - D.index w = d ∧ ¬ P z).card := by
  unfold shiftBadPairs
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ i ∈ W ×ˢ W,
    if D.index i.2 - D.index i.1 = d ∧ ¬ P i.2 then 1 else 0) = _
  rw [Finset.sum_product]
  simp_rw [Finset.card_filter]

private lemma shiftBadPairs_card_second {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (P : X → Prop) [DecidablePred P] :
    (shiftBadPairs D W d P).card =
      ∑ z ∈ W, (W.filter fun w =>
        D.index z - D.index w = d ∧ ¬ P z).card := by
  unfold shiftBadPairs
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ i ∈ W ×ˢ W,
    if D.index i.2 - D.index i.1 = d ∧ ¬ P i.2 then 1 else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp_rw [Finset.card_filter]

private lemma first_slice_eq_shiftedBadCount {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {W : Finset X} (hW : D.FibreSaturated W) (d : ZMod N) (P : X → Prop)
    [DecidablePred P]
    {w : X} (hw : w ∈ W ∩ D.shift W (-d)) :
    (W.filter fun z => D.index z - D.index w = d ∧ ¬ P z).card =
      shiftedBadCount D d P w := by
  unfold shiftedBadCount
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, mem_fibre_iff]
  constructor
  · rintro ⟨_, hdiff, hbad⟩
    exact ⟨by simpa [add_comm] using sub_eq_iff_eq_add.mp hdiff, hbad⟩
  · rintro ⟨hzindex, hbad⟩
    exact ⟨shifted_fibre_subset D hW d hw (mem_fibre_iff D _ _ |>.mpr hzindex),
      sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hzindex), hbad⟩

private lemma second_slice_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {W : Finset X} (d : ZMod N) (P : X → Prop) [DecidablePred P] (m : Nat)
    (hupper : ∀ w, w ∈ W → D.fibreSize w ≤ 2 * m) (z : X) :
    (W.filter fun w => D.index z - D.index w = d ∧ ¬ P z).card ≤
      if ¬ P z then 2 * m else 0 := by
  by_cases hzbad : ¬ P z
  · rw [if_pos hzbad]
    by_cases hs : (W.filter fun w => D.index z - D.index w = d ∧ ¬ P z).Nonempty
    · obtain ⟨w, hw⟩ := hs
      have hwW : w ∈ W := (Finset.mem_filter.mp hw).1
      have hsub : (W.filter fun x => D.index z - D.index x = d ∧ ¬ P z) ⊆
          D.fibre (D.index w) := by
        intro x hx
        have hxrel := (Finset.mem_filter.mp hx).2.1
        have hwrel := (Finset.mem_filter.mp hw).2.1
        apply (mem_fibre_iff D _ _).mpr
        exact sub_right_inj.mp (hxrel.trans hwrel.symm)
      exact (Finset.card_le_card hsub).trans (hupper w hwW)
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty] using
        Nat.zero_le (2 * m)
  · rw [if_neg hzbad]
    have hzP : P z := not_not.mp hzbad
    simp [hzP]

def shiftEligible {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) : Finset X :=
  W ∩ D.shift W (-d)

private def shiftExceptional {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (theta : Real) (P : X → Prop) : Finset X := by
  classical
  exact (shiftEligible D W d).filter fun w =>
    ¬ AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P

/-- Double-counting bound for eligible points whose shifted fibre has too
many exceptions. -/
private lemma shiftExceptional_card_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (d : ZMod N) (theta : Real) (P : X → Prop)
    (hW : D.FibreSaturated W) (hvar : VariesByFactorAtMostTwo W D.fibreSize)
    (htheta : 0 < theta) (hP : AlmostEvery (1 - theta) W P) :
    ((shiftExceptional D W d theta P).card : Real) ≤
      Real.sqrt theta * W.card := by
  classical
  let H := shiftExceptional D W d theta P
  by_cases hHempty : H = ∅
  · rw [show (shiftExceptional D W d theta P).card = 0 by simp [H, hHempty], Nat.cast_zero]
    positivity
  have hHne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hHempty
  have hHW : H ⊆ W := fun w hw => (Finset.mem_inter.mp (Finset.mem_filter.mp hw).1).1
  have hWne : W.Nonempty := hHne.mono hHW
  let Rvals : Finset Nat := W.image D.fibreSize
  have hRne : Rvals.Nonempty := hWne.image _
  let m : Nat := Rvals.min' hRne
  have hm_le (w : X) (hw : w ∈ W) : m ≤ D.fibreSize w := by
    exact Finset.min'_le Rvals (D.fibreSize w)
      (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  obtain ⟨xmin, hxminW, hxmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem Rvals hRne)
  have hxmin_eq : D.fibreSize xmin = m := hxmin
  have hmpos : 0 < m := by
    rw [← hxmin_eq]
    unfold MultifunctionDomain.fibreSize
    exact Finset.card_pos.mpr ⟨xmin, (by simp)⟩
  have hupper (w : X) (hw : w ∈ W) : D.fibreSize w ≤ 2 * m := by
    simpa only [← hxmin_eq] using hvar w hw xmin hxminW
  have hspos : 0 < Real.sqrt theta := Real.sqrt_pos.2 htheta
  have hheavy (w : X) (hw : w ∈ H) :
      2 * Real.sqrt theta * m < (shiftedBadCount D d P w : Real) := by
    have hwE : w ∈ shiftEligible D W d := (Finset.mem_filter.mp hw).1
    obtain ⟨u, huW, huindex⟩ :=
      exists_shifted_representative D d (by simpa [shiftEligible] using hwE)
    have hcard_eq : (D.fibre (D.index w + d)).card = D.fibreSize u := by
      unfold MultifunctionDomain.fibreSize
      rw [huindex]
    have hm_target : (m : Real) ≤ (D.fibre (D.index w + d)).card := by
      rw [hcard_eq]
      exact_mod_cast hm_le u huW
    have hfail := (Finset.mem_filter.mp hw).2
    have hbad := bad_card_lt_of_not_almostEvery
      (2 * Real.sqrt theta) (D.fibre (D.index w + d)) P hfail
    unfold shiftedBadCount
    exact lt_of_le_of_lt (by
      exact mul_le_mul_of_nonneg_left hm_target (mul_nonneg (by positivity) hspos.le)) hbad
  have hsumNat :
      (∑ w ∈ H, shiftedBadCount D d P w) ≤ (shiftBadPairs D W d P).card := by
    calc
      (∑ w ∈ H, shiftedBadCount D d P w) =
          ∑ w ∈ H, (W.filter fun z =>
            D.index z - D.index w = d ∧ ¬ P z).card := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [first_slice_eq_shiftedBadCount D hW d P]
        simpa [H, shiftExceptional, shiftEligible] using (Finset.mem_filter.mp hw).1
      _ ≤ ∑ w ∈ W, (W.filter fun z =>
          D.index z - D.index w = d ∧ ¬ P z).card :=
        Finset.sum_le_sum_of_subset hHW
      _ = (shiftBadPairs D W d P).card :=
        (shiftBadPairs_card_first D W d P).symm
  have hdeltaLower :
      (H.card : Real) * (2 * Real.sqrt theta * m) <
        (shiftBadPairs D W d P).card := by
    have hstrict :
        (∑ w ∈ H, 2 * Real.sqrt theta * m) <
          ∑ w ∈ H, (shiftedBadCount D d P w : Real) :=
      Finset.sum_lt_sum_of_nonempty hHne fun w hw => hheavy w hw
    have hsumReal :
        (∑ w ∈ H, (shiftedBadCount D d P w : Real)) ≤
          ((shiftBadPairs D W d P).card : Real) := by
      exact_mod_cast hsumNat
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_mul] using
      hstrict.trans_le hsumReal
  have hdeltaUpperNat :
      (shiftBadPairs D W d P).card ≤
        (W.filter fun z => ¬ P z).card * (2 * m) := by
    calc
      (shiftBadPairs D W d P).card =
          ∑ z ∈ W, (W.filter fun w =>
            D.index z - D.index w = d ∧ ¬ P z).card :=
        shiftBadPairs_card_second D W d P
      _ ≤ ∑ z ∈ W, if ¬ P z then 2 * m else 0 :=
        Finset.sum_le_sum fun z _ => second_slice_le D d P m hupper z
      _ = (W.filter fun z => ¬ P z).card * (2 * m) := by
        rw [Finset.card_filter, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        split <;> simp_all
  have hbadW := almostEvery_bad_card_le theta W P hP
  have hdeltaUpper :
      ((shiftBadPairs D W d P).card : Real) ≤
        (theta * W.card) * (2 * m) :=
    (show ((shiftBadPairs D W d P).card : Real) ≤ ((W.filter fun z => ¬ P z).card : Real) * (2 * m)
      by exact_mod_cast hdeltaUpperNat).trans (mul_le_mul_of_nonneg_right hbadW (by positivity))
  by_contra hcard
  rw [← Real.sq_sqrt htheta.le] at hdeltaUpper
  have := mul_lt_mul_of_pos_right (lt_of_not_ge hcard)
    (by positivity : 0 < 2 * Real.sqrt theta * (m : Real))
  linarith

/-! ### Lemma 10.8 -/

/-- The double count actually retains membership in the large overlap set;
this stronger form is what the two-step argument for Lemma 10.9 uses. -/
lemma shift_almostEvery_eligible {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (B : Finset (ZMod N)) (eta theta : Real) (P : X → Prop)
    (hregular : IsSection10ShiftRegular D W B eta) (htheta : 0 < theta)
    (hP : AlmostEvery (1 - theta) W P) (d : ZMod N) (hd : d ∈ B) :
    AlmostEvery (1 - Real.sqrt theta - eta) W fun w =>
      w ∈ shiftEligible D W d ∧
        AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P := by
  classical
  rcases hregular with ⟨hW, hsym, hvar, hoverlap⟩
  let Q : X → Prop := fun w =>
    AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P
  -- the eligible points split into those satisfying `Q` and the exceptional ones
  have hpart : (((shiftEligible D W d).filter Q).card : Real) +
      (shiftExceptional D W d theta P).card = (shiftEligible D W d).card := by
    exact_mod_cast card_filter_add_card_filter_not Q
  have hE : (1 - eta) * W.card ≤ ((shiftEligible D W d).card : Real) :=
    hoverlap (-d) ((hsym d).mp hd)
  have hX := shiftExceptional_card_le D W d theta P hW hvar htheta hP
  rw [AlmostEvery, filter_congr_decidable]
  refine le_trans (by linarith) (Nat.cast_le.mpr (card_le_card
    (s := (shiftEligible D W d).filter Q) fun w hw => mem_filter.mpr
      ⟨(mem_inter.mp (mem_filter.mp hw).1).1, mem_filter.mp hw⟩))

/-! ### Lemma 10.9 -/

private lemma almostEvery_shiftEligible {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (B : Finset (ZMod N)) (eta : Real)
    (hregular : IsSection10ShiftRegular D W B eta)
    (d : ZMod N) (hd : d ∈ B) :
    AlmostEvery (1 - eta) W fun w => w ∈ shiftEligible D W d := by
  rcases hregular with ⟨_, hsym, _, hoverlap⟩
  have hnegd : -d ∈ B := (hsym d).mp hd
  have hover := hoverlap (-d) hnegd
  have heq : (W.filter fun w => w ∈ shiftEligible D W d) =
      shiftEligible D W d := by
    ext w
    simp only [Finset.mem_filter, shiftEligible, Finset.mem_inter]
    aesop
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable, heq]
  exact hover

private def localDifferenceGood {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (psi : ZMod N → ZMod N) (theta : Real)
    (d : ZMod N) (w : X) : Prop :=
  AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z =>
    phi z - phi w = psi d

/-- A non-vacuous version of the two-step argument. Besides shifting the
second local model, it shifts the assertion that the terminal fibre exists. -/
private lemma twoStep_localDifference_nonempty {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (W : Finset X) (B : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (eta theta rho : Real)
    (hregular : IsSection10ShiftRegular D W B eta) (hrho : 0 < rho)
    (htheta_eta_rho : theta + eta ≤ rho)
    (houter : theta + (Real.sqrt rho + eta) ≤ 3 * Real.sqrt theta)
    (hmiddle : theta + 2 * Real.sqrt rho < 1)
    (d₁ d₂ : ZMod N) (hd₁ : d₁ ∈ B) (hd₂ : d₂ ∈ B)
    (hlocal₁ : AlmostEvery (1 - theta) W
      (localDifferenceGood D phi psi theta d₁))
    (hlocal₂ : AlmostEvery (1 - theta) W
      (localDifferenceGood D phi psi theta d₂)) :
    AlmostEvery (1 - 3 * Real.sqrt theta) W fun w =>
      (D.fibre (D.index w + d₁ + d₂)).Nonempty ∧
      AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
        phi z - phi w = psi d₁ + psi d₂ := by
  -- almost every `w` is good for `d₁`, and almost all of its `d₁`-fibre is good for `d₂`
  have hS := shift_almostEvery_eligible D W B eta rho _ hregular hrho
    (almostEvery_weaken_error _ _ W _ htheta_eta_rho (almostEvery_and _ _ W _ _ hlocal₂
      (almostEvery_shiftEligible D W B eta hregular d₂ hd₂))) d₁ hd₁
  rw [sub_sub] at hS
  refine almostEvery_mono _ W _ _ (almostEvery_weaken_error _ _ W _ houter
    (almostEvery_and _ _ W _ _ hlocal₁ hS)) fun w _ hw => ?_
  obtain ⟨hQ₁, hwE, hR₂⟩ := hw
  -- a point `w'` of the `d₁`-fibre that is good for `d₂` and has a nonempty `d₂`-fibre
  obtain ⟨u, -, hu⟩ := exists_shifted_representative D d₁ hwE
  obtain ⟨w', hw', hrel₁, hQ₂, hw'E⟩ := exists_and_of_almostEvery _ _ _ _ _
    ⟨u, (mem_fibre_iff D _ _).mpr hu⟩ hmiddle hQ₁ hR₂
  obtain ⟨z₀, -, hz₀⟩ := exists_shifted_representative D d₂ hw'E
  have hfib : D.index w' + d₂ = D.index w + d₁ + d₂ := by
    rw [(mem_fibre_iff D _ _).mp hw']
  refine ⟨⟨z₀, (mem_fibre_iff D _ _).mpr (hz₀.trans hfib)⟩, ?_⟩
  have hQ₂' : AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
      phi z - phi w' = psi d₂ := hfib ▸ hQ₂
  exact almostEvery_mono _ _ _ _ hQ₂' fun z _ hz => by linear_combination hz + hrel₁

theorem lemma_10_9_holds : lemma_10_9 := by
  intro N _ X _ _ D phi W B B' psi eta theta hWne hregular hmodel hsmall
  obtain ⟨hB'sub, -, hlocal⟩ := hmodel
  refine isAddFreimanHom_two.mpr ⟨Set.mapsTo_univ _ _,
    fun d₁ hd₁ d₂ hd₂ d₃ hd₃ d₄ hd₄ hadd => ?_⟩
  -- `0 ≤ eta` by the overlap bound; then `theta < 1 / 36` and `eta ≤ theta / 10`
  have heta : 0 ≤ eta := by
    have h : ((W ∩ D.shift W d₁).card : Real) ≤ W.card := by
      exact_mod_cast card_le_card inter_subset_left
    nlinarith [hregular.2.2.2 d₁ (hB'sub hd₁),
      (by exact_mod_cast hWne.card_pos : (0 : Real) < W.card)]
  have hθ : theta = 10 * eta ^ ((1 : Real) / 5) := rfl
  have hθ0 : 0 ≤ theta := by positivity
  have hθ1 : theta < 1 / 36 := by
    have h := Real.lt_sq_of_sqrt_lt (show Real.sqrt theta < 1 / 6 by linarith)
    norm_num at h
    linarith
  have hηθ : eta ≤ theta / 10 := by
    have h := (Real.rpow_lt_one_iff' heta (by norm_num : (0 : Real) < 1 / 5)).mp (by linarith)
    linarith [Real.self_le_rpow_of_le_one heta h.le (by norm_num : (1 : Real) / 5 ≤ 1)]
  -- Raising `theta` to some `θ ∈ (0, 1/36)` only weakens the local model, and `0 < θ` lets the
  -- two-step argument run without a separate exact case `theta = 0`.
  obtain ⟨θ, hθθ, hθpos, hθ36⟩ : ∃ θ, theta ≤ θ ∧ 0 < θ ∧ θ < 1 / 36 :=
    ⟨(theta + 1 / 36) / 2, by linarith, by linarith, by linarith⟩
  have hs := Real.sqrt_pos.2 hθpos
  have hsq := Real.sq_sqrt hθpos.le
  have hs6 : Real.sqrt θ < 1 / 6 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num; linarith)
  have hθs : θ < Real.sqrt θ / 6 := by linarith [mul_pos hs (sub_pos.mpr hs6)]
  have hρs : Real.sqrt (θ + eta) ≤ 2 * Real.sqrt θ :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by linarith⟩
  have hloc (d : ZMod N) (hd : d ∈ B') :
      AlmostEvery (1 - θ) W (localDifferenceGood D phi psi θ d) :=
    almostEvery_weaken_error _ _ W _ hθθ (almostEvery_mono _ W _ _ (hlocal d hd)
      fun _ _ h => almostEvery_weaken_error _ _ _ _ hθθ h)
  have hpair (a b : ZMod N) (ha : a ∈ B') (hb : b ∈ B') :=
    twoStep_localDifference_nonempty D phi W B psi eta θ (θ + eta) hregular (by linarith)
      le_rfl (by linarith) (by linarith) a b (hB'sub ha) (hB'sub hb) (hloc a ha) (hloc b hb)
  obtain ⟨w, -, ⟨hne, h₁₂⟩, -, h₃₄⟩ := exists_and_of_almostEvery _ _ W _ _ hWne
    (by linarith) (hpair d₁ d₂ hd₁ hd₂) (hpair d₃ d₄ hd₃ hd₄)
  rw [show D.index w + d₃ + d₄ = D.index w + d₁ + d₂ by
    rw [add_assoc, add_assoc, hadd]] at h₃₄
  obtain ⟨z, -, hz₁₂, hz₃₄⟩ := exists_and_of_almostEvery _ _ _ _ _ hne (by linarith) h₁₂ h₃₄
  exact hz₁₂.symm.trans hz₃₄

end LeanProofs.GowersSzemeredi
