import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure

/-!
# Shifting almost-everywhere properties in Section 10

This file proves the double-counting shift lemma used to construct the local
Freiman homomorphism.  The proof uses the fibre saturation and symmetry
hypotheses recorded in `IsSection10ShiftRegular`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma mem_fibre_iff {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (s : ZMod N) (x : X) : x ∈ D.fibre s ↔ D.index x = s := by
  classical
  simp [MultifunctionDomain.fibre]

private lemma self_mem_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (x : X) : x ∈ D.fibre (D.index x) := by
  simp

private lemma fibreSize_pos {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (x : X) : 0 < D.fibreSize x := by
  unfold MultifunctionDomain.fibreSize
  exact Finset.card_pos.mpr ⟨x, self_mem_fibre D x⟩

private lemma fibreSize_eq_of_index_eq {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    {x y : X} (hxy : D.index x = D.index y) :
    D.fibreSize x = D.fibreSize y := by
  simp only [MultifunctionDomain.fibreSize, hxy]

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
  classical
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
  classical
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
  classical
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
  classical
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) + ((U.filter fun x => ¬ P x).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable]
  nlinarith

private lemma almostEvery_mono {X : Type*} [DecidableEq X]
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
  have hcard : (0 : Real) ≤ U.card := by positivity
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
  have hgood : (0 : Real) < ((U.filter fun x => P x ∧ Q x).card : Real) := by
    exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hab) hUcard) hAnd
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hgood)
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

private lemma of_almostEvery_one {X : Type*} [DecidableEq X]
    (U : Finset X) (P : X → Prop) (hP : AlmostEvery 1 U P)
    {x : X} (hx : x ∈ U) : P x := by
  classical
  have hcard : U.card ≤ (U.filter P).card := by
    unfold AlmostEvery at hP
    rw [Finset.filter_congr_decidable] at hP
    exact_mod_cast (by simpa using hP)
  have heq : U.filter P = U :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard
  exact (Finset.mem_filter.mp (heq.symm ▸ hx)).2

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
  classical
  unfold shiftBadPairs
  rw [Finset.filter_congr_decidable]
  rw [Finset.card_filter]
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
  classical
  unfold shiftBadPairs
  rw [Finset.filter_congr_decidable]
  rw [Finset.card_filter]
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
  classical
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
  classical
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
        apply sub_right_inj.mp
        exact hxrel.trans hwrel.symm
      exact (Finset.card_le_card hsub).trans (hupper w hwW)
    · simpa only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty] using
        Nat.zero_le (2 * m)
  · rw [if_neg hzbad]
    have hzP : P z := not_not.mp hzbad
    simp [hzP]

private def shiftEligible {N : Nat} [NeZero N]
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
  · rw [show (shiftExceptional D W d theta P).card = 0 by simp [H, hHempty]]
    norm_num only [Nat.cast_zero]
    have hWcard : (0 : Real) ≤ W.card := by positivity
    exact mul_nonneg (Real.sqrt_nonneg theta) hWcard
  have hHne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hHempty
  have hHW : H ⊆ W := by
    intro w hw
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hw).1).1
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
    exact fibreSize_pos D xmin
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
      have hm_target_nat : m ≤ (D.fibre (D.index w + d)).card := by
        rw [hcard_eq]
        exact hm_le u huW
      exact_mod_cast hm_target_nat
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
        apply Finset.sum_congr rfl
        intro w hw
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
        apply Finset.sum_congr rfl
        intro z _
        split <;> simp_all
  have hbadW := almostEvery_bad_card_le theta W P hP
  have hdeltaUpper :
      ((shiftBadPairs D W d P).card : Real) ≤
        (theta * W.card) * (2 * m) := by
    have hupperReal :
        ((shiftBadPairs D W d P).card : Real) ≤
          ((W.filter fun z => ¬ P z).card : Real) * (2 * m) := by
      exact_mod_cast hdeltaUpperNat
    exact hupperReal.trans
      (mul_le_mul_of_nonneg_right hbadW (by positivity))
  by_contra hcard
  have hcardgt : Real.sqrt theta * W.card < (H.card : Real) := lt_of_not_ge hcard
  have hfactorpos : 0 < 2 * Real.sqrt theta * (m : Real) := by positivity
  have hcontra :
      (Real.sqrt theta * W.card) * (2 * Real.sqrt theta * m) <
        (theta * W.card) * (2 * m) :=
    (mul_lt_mul_of_pos_right hcardgt hfactorpos).trans
      (hdeltaLower.trans_le hdeltaUpper)
  have hsquare : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt htheta.le
  have heq :
      (Real.sqrt theta * W.card) * (2 * Real.sqrt theta * m) =
        (theta * W.card) * (2 * m) := by
    calc
      (Real.sqrt theta * W.card) * (2 * Real.sqrt theta * m) =
          (Real.sqrt theta) ^ 2 * W.card * (2 * m) := by ring
      _ = theta * W.card * (2 * m) := by rw [hsquare]
  rw [heq] at hcontra
  exact lt_irrefl _ hcontra

/-! ### Lemma 10.8 -/

/-- The double count actually retains membership in the large overlap set;
this stronger form is what the two-step argument for Lemma 10.9 uses. -/
private lemma shift_almostEvery_eligible {N : Nat} [NeZero N]
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
  have hnegd : -d ∈ B := (hsym d).mp hd
  have heligible :
      (1 - eta) * W.card ≤ ((shiftEligible D W d).card : Real) := by
    simpa only [shiftEligible] using hoverlap (-d) hnegd
  have hexceptional :
      ((shiftExceptional D W d theta P).card : Real) ≤
        Real.sqrt theta * W.card :=
    shiftExceptional_card_le D W d theta P hW hvar htheta hP
  have hpartNat := Finset.card_filter_add_card_filter_not Q
    (s := shiftEligible D W d)
  have hpart :
      (((shiftEligible D W d).filter Q).card : Real) +
          ((shiftExceptional D W d theta P).card : Real) =
        (shiftEligible D W d).card := by
    have hcast :
        (((shiftEligible D W d).filter Q).card : Real) +
            (((shiftEligible D W d).filter fun w => ¬ Q w).card : Real) =
          (shiftEligible D W d).card := by
      exact_mod_cast hpartNat
    simpa only [Q, shiftExceptional] using hcast
  have hgoodEq :
      (W.filter fun w => w ∈ shiftEligible D W d ∧ Q w) =
        (shiftEligible D W d).filter Q := by
    ext w
    simp only [Finset.mem_filter, shiftEligible, Finset.mem_inter]
    aesop
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable]
  change (1 - Real.sqrt theta - eta) * (W.card : Real) ≤
    ((W.filter fun w => w ∈ shiftEligible D W d ∧ Q w).card : Real)
  rw [hgoodEq]
  nlinarith

theorem lemma_10_8_holds : lemma_10_8 := by
  classical
  intro N _ X _ _ D W B eta theta P hregular htheta hP d hd
  exact almostEvery_mono (1 - Real.sqrt theta - eta) W
    (fun w => w ∈ shiftEligible D W d ∧
      AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P)
    (fun w => AlmostEvery (1 - 2 * Real.sqrt theta) (D.fibre (D.index w + d)) P)
    (shift_almostEvery_eligible D W B eta theta P hregular htheta hP d hd)
    (fun _ _ h => h.2)

/-! ### Lemma 10.9 -/

private lemma almostEvery_shiftEligible {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (W : Finset X) (B : Finset (ZMod N)) (eta : Real)
    (hregular : IsSection10ShiftRegular D W B eta)
    (d : ZMod N) (hd : d ∈ B) :
    AlmostEvery (1 - eta) W fun w => w ∈ shiftEligible D W d := by
  classical
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

/-- Combine the local models in two directions into an almost-everywhere
model for their sum. -/
private lemma twoStep_localDifference {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (W : Finset X) (B : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (eta theta tau : Real)
    (hregular : IsSection10ShiftRegular D W B eta) (htau : 0 < tau)
    (htheta_tau : theta ≤ tau)
    (hround : theta + (Real.sqrt tau + eta) ≤ 3 * Real.sqrt tau)
    (hintermediate : theta + 2 * Real.sqrt tau < 1)
    (d₁ d₂ : ZMod N) (hd₁ : d₁ ∈ B)
    (hlocal₁ : AlmostEvery (1 - theta) W
      (localDifferenceGood D phi psi theta d₁))
    (hlocal₂ : AlmostEvery (1 - theta) W
      (localDifferenceGood D phi psi theta d₂)) :
    AlmostEvery (1 - 3 * Real.sqrt tau) W fun w =>
      AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
        phi z - phi w = psi d₁ + psi d₂ := by
  classical
  let Q₁ : X → Prop := localDifferenceGood D phi psi theta d₁
  let Q₂ : X → Prop := localDifferenceGood D phi psi theta d₂
  let S : X → Prop := fun w =>
    w ∈ shiftEligible D W d₁ ∧
      AlmostEvery (1 - 2 * Real.sqrt tau) (D.fibre (D.index w + d₁)) Q₂
  have hlocal₂tau : AlmostEvery (1 - tau) W Q₂ := by
    exact almostEvery_weaken_error theta tau W Q₂ htheta_tau hlocal₂
  have hshift : AlmostEvery (1 - (Real.sqrt tau + eta)) W S := by
    have hs := shift_almostEvery_eligible D W B eta tau Q₂ hregular htau
      hlocal₂tau d₁ hd₁
    convert hs using 1
    ring
  have hboth : AlmostEvery (1 - (theta + (Real.sqrt tau + eta))) W
      (fun w => Q₁ w ∧ S w) :=
    almostEvery_and theta (Real.sqrt tau + eta) W Q₁ S hlocal₁ hshift
  have hboth' : AlmostEvery (1 - 3 * Real.sqrt tau) W
      (fun w => Q₁ w ∧ S w) :=
    almostEvery_weaken_error (theta + (Real.sqrt tau + eta))
      (3 * Real.sqrt tau) W (fun w => Q₁ w ∧ S w) hround hboth
  apply almostEvery_mono (1 - 3 * Real.sqrt tau) W (fun w => Q₁ w ∧ S w)
  · exact hboth'
  · intro w hwW hw
    rcases hw with ⟨hQ₁, hwEligible, hQ₂⟩
    have hwEligible' : w ∈ W ∩ D.shift W (-d₁) := by
      simpa only [shiftEligible] using hwEligible
    obtain ⟨u, huW, huindex⟩ := exists_shifted_representative D d₁ hwEligible'
    have huFibre : u ∈ D.fibre (D.index w + d₁) :=
      (mem_fibre_iff D _ _).mpr huindex
    obtain ⟨w', hw'Fibre, hrel₁, hQ₂w'⟩ :=
      exists_and_of_almostEvery theta (2 * Real.sqrt tau)
        (D.fibre (D.index w + d₁))
        (fun w' => phi w' - phi w = psi d₁) Q₂
        ⟨u, huFibre⟩ hintermediate hQ₁ hQ₂
    have hw'index : D.index w' = D.index w + d₁ :=
      (mem_fibre_iff D _ _).mp hw'Fibre
    have hQ₂w'' :
        AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
          phi z - phi w' = psi d₂ := by
      simpa only [Q₂, localDifferenceGood, hw'index, add_assoc] using hQ₂w'
    exact almostEvery_mono (1 - theta) (D.fibre (D.index w + d₁ + d₂))
      (fun z => phi z - phi w' = psi d₂)
      (fun z => phi z - phi w = psi d₁ + psi d₂) hQ₂w''
      (fun z _ hrel₂ => by
        calc
          phi z - phi w = (phi z - phi w') + (phi w' - phi w) := by abel
          _ = psi d₂ + psi d₁ := by rw [hrel₂, hrel₁]
          _ = psi d₁ + psi d₂ := add_comm _ _)

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
  classical
  let Q₁ : X → Prop := localDifferenceGood D phi psi theta d₁
  let Q₂ : X → Prop := localDifferenceGood D phi psi theta d₂
  let E₂ : X → Prop := fun w => w ∈ shiftEligible D W d₂
  let R₂ : X → Prop := fun w => Q₂ w ∧ E₂ w
  let S : X → Prop := fun w =>
    w ∈ shiftEligible D W d₁ ∧
      AlmostEvery (1 - 2 * Real.sqrt rho) (D.fibre (D.index w + d₁)) R₂
  have hE₂ : AlmostEvery (1 - eta) W E₂ := by
    exact almostEvery_shiftEligible D W B eta hregular d₂ hd₂
  have hR₂base : AlmostEvery (1 - (theta + eta)) W R₂ := by
    exact almostEvery_and theta eta W Q₂ E₂ hlocal₂ hE₂
  have hR₂rho : AlmostEvery (1 - rho) W R₂ :=
    almostEvery_weaken_error (theta + eta) rho W R₂ htheta_eta_rho hR₂base
  have hshift : AlmostEvery (1 - (Real.sqrt rho + eta)) W S := by
    have hs := shift_almostEvery_eligible D W B eta rho R₂ hregular hrho
      hR₂rho d₁ hd₁
    convert hs using 1
    ring
  have hboth : AlmostEvery (1 - (theta + (Real.sqrt rho + eta))) W
      (fun w => Q₁ w ∧ S w) :=
    almostEvery_and theta (Real.sqrt rho + eta) W Q₁ S hlocal₁ hshift
  have hboth' : AlmostEvery (1 - 3 * Real.sqrt theta) W
      (fun w => Q₁ w ∧ S w) :=
    almostEvery_weaken_error (theta + (Real.sqrt rho + eta))
      (3 * Real.sqrt theta) W (fun w => Q₁ w ∧ S w) houter hboth
  apply almostEvery_mono (1 - 3 * Real.sqrt theta) W (fun w => Q₁ w ∧ S w)
  · exact hboth'
  · intro w hwW hw
    rcases hw with ⟨hQ₁, hwEligible, hR₂⟩
    have hwEligible' : w ∈ W ∩ D.shift W (-d₁) := by
      simpa only [shiftEligible] using hwEligible
    obtain ⟨u, huW, huindex⟩ := exists_shifted_representative D d₁ hwEligible'
    have huFibre : u ∈ D.fibre (D.index w + d₁) :=
      (mem_fibre_iff D _ _).mpr huindex
    obtain ⟨w', hw'Fibre, hrel₁, hQ₂w', hw'Eligible⟩ :=
      exists_and_of_almostEvery theta (2 * Real.sqrt rho)
        (D.fibre (D.index w + d₁))
        (fun w' => phi w' - phi w = psi d₁) R₂
        ⟨u, huFibre⟩ hmiddle hQ₁ hR₂
    have hw'index : D.index w' = D.index w + d₁ :=
      (mem_fibre_iff D _ _).mp hw'Fibre
    have hw'Eligible' : w' ∈ W ∩ D.shift W (-d₂) := by
      simpa only [R₂, E₂, shiftEligible] using hw'Eligible
    obtain ⟨z₀, hz₀W, hz₀index⟩ :=
      exists_shifted_representative D d₂ hw'Eligible'
    have hz₀Fibre : z₀ ∈ D.fibre (D.index w + d₁ + d₂) := by
      apply (mem_fibre_iff D _ _).mpr
      rw [hz₀index, hw'index, add_assoc]
    refine ⟨⟨z₀, hz₀Fibre⟩, ?_⟩
    have hQ₂w'' :
        AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
          phi z - phi w' = psi d₂ := by
      simpa only [R₂, Q₂, localDifferenceGood, hw'index, add_assoc] using hQ₂w'
    exact almostEvery_mono (1 - theta) (D.fibre (D.index w + d₁ + d₂))
      (fun z => phi z - phi w' = psi d₂)
      (fun z => phi z - phi w = psi d₁ + psi d₂) hQ₂w''
      (fun z _ hrel₂ => by
        calc
          phi z - phi w = (phi z - phi w') + (phi w' - phi w) := by abel
          _ = psi d₂ + psi d₁ := by rw [hrel₂, hrel₁]
          _ = psi d₁ + psi d₂ := add_comm _ _)

/-- The zero-error endpoint of the two-step argument. -/
private lemma twoStep_localDifference_exact {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (W : Finset X) (B : Finset (ZMod N))
    (psi : ZMod N → ZMod N)
    (hregular : IsSection10ShiftRegular D W B 0)
    (d₁ d₂ : ZMod N) (hd₁ : d₁ ∈ B) (hd₂ : d₂ ∈ B)
    (hlocal₁ : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₁))
    (hlocal₂ : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₂))
    (w : X) (hwW : w ∈ W) :
    (D.fibre (D.index w + d₁ + d₂)).Nonempty ∧
      ∀ z ∈ D.fibre (D.index w + d₁ + d₂),
        phi z - phi w = psi d₁ + psi d₂ := by
  classical
  let E₁ : X → Prop := fun x => x ∈ shiftEligible D W d₁
  have hE₁ : AlmostEvery 1 W E₁ := by
    simpa only [sub_zero] using almostEvery_shiftEligible D W B 0 hregular d₁ hd₁
  have hwEligible : w ∈ W ∩ D.shift W (-d₁) := by
    simpa only [E₁, shiftEligible] using of_almostEvery_one W E₁ hE₁ hwW
  obtain ⟨w', hw'W, hw'index⟩ := exists_shifted_representative D d₁ hwEligible
  have hw'Fibre : w' ∈ D.fibre (D.index w + d₁) :=
    (mem_fibre_iff D _ _).mpr hw'index
  have hQ₁ := of_almostEvery_one W (localDifferenceGood D phi psi 0 d₁) hlocal₁ hwW
  have hrel₁ : phi w' - phi w = psi d₁ := by
    exact of_almostEvery_one (D.fibre (D.index w + d₁))
      (fun z => phi z - phi w = psi d₁) (by simpa [localDifferenceGood] using hQ₁)
      hw'Fibre
  let E₂ : X → Prop := fun x => x ∈ shiftEligible D W d₂
  have hE₂ : AlmostEvery 1 W E₂ := by
    simpa only [sub_zero] using almostEvery_shiftEligible D W B 0 hregular d₂ hd₂
  have hw'Eligible : w' ∈ W ∩ D.shift W (-d₂) := by
    simpa only [E₂, shiftEligible] using
      of_almostEvery_one W E₂ hE₂ hw'W
  obtain ⟨z₀, hz₀W, hz₀index⟩ :=
    exists_shifted_representative D d₂ hw'Eligible
  have hz₀Fibre : z₀ ∈ D.fibre (D.index w + d₁ + d₂) := by
    apply (mem_fibre_iff D _ _).mpr
    rw [hz₀index, hw'index, add_assoc]
  refine ⟨⟨z₀, hz₀Fibre⟩, ?_⟩
  have hQ₂ := of_almostEvery_one W (localDifferenceGood D phi psi 0 d₂) hlocal₂ hw'W
  intro z hzFibre
  have hrel₂ : phi z - phi w' = psi d₂ := by
    exact of_almostEvery_one (D.fibre (D.index w + d₁ + d₂))
      (fun z => phi z - phi w' = psi d₂) (by
        simpa only [localDifferenceGood, hw'index, add_assoc, sub_zero] using hQ₂) hzFibre
  calc
    phi z - phi w = (phi z - phi w') + (phi w' - phi w) := by abel
    _ = psi d₂ + psi d₁ := by rw [hrel₂, hrel₁]
    _ = psi d₁ + psi d₂ := add_comm _ _

theorem lemma_10_9_holds : lemma_10_9 := by
  classical
  intro N _ X _ _ D phi W B B' psi eta
  dsimp only
  intro hWne hregular hmodel hsmall
  let theta : Real := 10 * eta ^ ((1 : Real) / 5)
  change IsSection10LocalDifferenceModel D phi W B B' psi theta at hmodel
  change 6 * Real.sqrt theta < 1 at hsmall
  rcases hmodel with ⟨hB'sub, _, hlocal⟩
  unfold FreimanHom
  rw [isAddFreimanHom_two]
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ d₃ hd₃ d₄ hd₄ hadd
  change d₁ ∈ B' at hd₁
  change d₂ ∈ B' at hd₂
  change d₃ ∈ B' at hd₃
  change d₄ ∈ B' at hd₄
  have hd₁B : d₁ ∈ B := hB'sub hd₁
  have hd₂B : d₂ ∈ B := hB'sub hd₂
  have hd₃B : d₃ ∈ B := hB'sub hd₃
  have hd₄B : d₄ ∈ B := hB'sub hd₄
  have hregularParts := hregular
  rcases hregularParts with ⟨_, _, _, hoverlap⟩
  have hover := hoverlap d₁ hd₁B
  have hinterNat : (W ∩ D.shift W d₁).card ≤ W.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hinter : ((W ∩ D.shift W d₁).card : Real) ≤ W.card := by
    exact_mod_cast hinterNat
  have hWcard : (0 : Real) < W.card := by
    exact_mod_cast Finset.card_pos.mpr hWne
  have heta : 0 ≤ eta := by nlinarith
  have hthetaDef : theta = 10 * eta ^ ((1 : Real) / 5) := rfl
  have hrootNonneg : 0 ≤ eta ^ ((1 : Real) / 5) := Real.rpow_nonneg heta _
  have hthetaNonneg : 0 ≤ theta := by rw [hthetaDef]; positivity
  have hsqrtNonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt hthetaNonneg
  have hthetaLtOne : theta < 1 := by nlinarith [hsquare]
  have hrootLtOne : eta ^ ((1 : Real) / 5) < 1 := by nlinarith [hthetaDef]
  have hetaLtOne : eta < 1 :=
    (Real.rpow_lt_one_iff' heta (by norm_num : (0 : Real) < (1 : Real) / 5)).mp
      hrootLtOne
  have hetaLeRoot : eta ≤ eta ^ ((1 : Real) / 5) :=
    Real.self_le_rpow_of_le_one heta hetaLtOne.le (by norm_num)
  have hetaLeThetaTenth : eta ≤ theta / 10 := by nlinarith [hthetaDef]
  have hlocal₁ := hlocal d₁ hd₁
  change AlmostEvery (1 - theta) W
    (localDifferenceGood D phi psi theta d₁) at hlocal₁
  have hlocal₂ := hlocal d₂ hd₂
  change AlmostEvery (1 - theta) W
    (localDifferenceGood D phi psi theta d₂) at hlocal₂
  have hlocal₃ := hlocal d₃ hd₃
  change AlmostEvery (1 - theta) W
    (localDifferenceGood D phi psi theta d₃) at hlocal₃
  have hlocal₄ := hlocal d₄ hd₄
  change AlmostEvery (1 - theta) W
    (localDifferenceGood D phi psi theta d₄) at hlocal₄
  by_cases hthetaZero : theta = 0
  · have hrootZero : eta ^ ((1 : Real) / 5) = 0 := by nlinarith [hthetaDef]
    have hetaZero : eta = 0 :=
      (Real.rpow_eq_zero heta (by norm_num : (1 : Real) / 5 ≠ 0)).mp hrootZero
    have hregularZero : IsSection10ShiftRegular D W B 0 := by
      simpa only [hetaZero] using hregular
    have hlocal₁Zero : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₁) := by
      simpa only [hthetaZero, sub_zero] using hlocal₁
    have hlocal₂Zero : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₂) := by
      simpa only [hthetaZero, sub_zero] using hlocal₂
    have hlocal₃Zero : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₃) := by
      simpa only [hthetaZero, sub_zero] using hlocal₃
    have hlocal₄Zero : AlmostEvery 1 W (localDifferenceGood D phi psi 0 d₄) := by
      simpa only [hthetaZero, sub_zero] using hlocal₄
    obtain ⟨w, hwW⟩ := hWne
    have hpair₁₂ := twoStep_localDifference_exact D phi W B psi hregularZero
      d₁ d₂ hd₁B hd₂B hlocal₁Zero hlocal₂Zero w hwW
    have hpair₃₄ := twoStep_localDifference_exact D phi W B psi hregularZero
      d₃ d₄ hd₃B hd₄B hlocal₃Zero hlocal₄Zero w hwW
    obtain ⟨z, hz⟩ := hpair₁₂.1
    have htargetEq : D.index w + d₁ + d₂ = D.index w + d₃ + d₄ := by
      simpa only [add_assoc] using congrArg (D.index w + ·) hadd
    have hz' := hz
    rw [htargetEq] at hz'
    exact (hpair₁₂.2 z hz).symm.trans (hpair₃₄.2 z hz')
  · have hthetaPos : 0 < theta := lt_of_le_of_ne hthetaNonneg (Ne.symm hthetaZero)
    have hsqrtPos : 0 < Real.sqrt theta := Real.sqrt_pos.2 hthetaPos
    have hthetaLtSqrtDivSix : theta < Real.sqrt theta / 6 := by
      have hprod := mul_pos hsqrtPos (sub_pos.mpr hsmall)
      nlinarith [hsquare]
    let rho : Real := theta + eta
    have hrhoPos : 0 < rho := by dsimp only [rho]; linarith
    have hrhoNonneg : 0 ≤ rho := hrhoPos.le
    have hrhoSquare : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrhoNonneg
    have hsqrtRhoNonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
    have hrhoLeFourTheta : rho ≤ 4 * theta := by
      dsimp only [rho]
      nlinarith [hetaLeThetaTenth]
    have hsqrtRhoLe : Real.sqrt rho ≤ 2 * Real.sqrt theta := by
      nlinarith [hrhoSquare, hsquare]
    have houter : theta + (Real.sqrt rho + eta) ≤ 3 * Real.sqrt theta := by
      nlinarith [hthetaLtSqrtDivSix, hetaLeThetaTenth, hsqrtRhoLe]
    have hmiddle : theta + 2 * Real.sqrt rho < 1 := by
      nlinarith [hthetaLtSqrtDivSix, hsqrtRhoLe, hsmall]
    have hpair₁₂ := twoStep_localDifference_nonempty D phi W B psi eta theta rho
      hregular hrhoPos le_rfl houter hmiddle d₁ d₂ hd₁B hd₂B hlocal₁ hlocal₂
    have hpair₃₄ := twoStep_localDifference_nonempty D phi W B psi eta theta rho
      hregular hrhoPos le_rfl houter hmiddle d₃ d₄ hd₃B hd₄B hlocal₃ hlocal₄
    let P₁₂ : X → Prop := fun w =>
      (D.fibre (D.index w + d₁ + d₂)).Nonempty ∧
      AlmostEvery (1 - theta) (D.fibre (D.index w + d₁ + d₂)) fun z =>
        phi z - phi w = psi d₁ + psi d₂
    let P₃₄ : X → Prop := fun w =>
      (D.fibre (D.index w + d₃ + d₄)).Nonempty ∧
      AlmostEvery (1 - theta) (D.fibre (D.index w + d₃ + d₄)) fun z =>
        phi z - phi w = psi d₃ + psi d₄
    have hpair₁₂' : AlmostEvery (1 - 3 * Real.sqrt theta) W P₁₂ := by
      simpa only [P₁₂] using hpair₁₂
    have hpair₃₄' : AlmostEvery (1 - 3 * Real.sqrt theta) W P₃₄ := by
      simpa only [P₃₄] using hpair₃₄
    have houterIntersect : 3 * Real.sqrt theta + 3 * Real.sqrt theta < 1 := by
      nlinarith
    obtain ⟨w, hwW, hw₁₂, hw₃₄⟩ :=
      exists_and_of_almostEvery (3 * Real.sqrt theta) (3 * Real.sqrt theta)
        W P₁₂ P₃₄ hWne houterIntersect hpair₁₂' hpair₃₄'
    rcases hw₁₂ with ⟨hfinalNonempty, hinner₁₂⟩
    rcases hw₃₄ with ⟨_, hinner₃₄⟩
    have htargetEq : D.index w + d₁ + d₂ = D.index w + d₃ + d₄ := by
      simpa only [add_assoc] using congrArg (D.index w + ·) hadd
    have hinner₃₄' : AlmostEvery (1 - theta)
        (D.fibre (D.index w + d₁ + d₂)) fun z =>
          phi z - phi w = psi d₃ + psi d₄ := by
      rw [htargetEq]
      exact hinner₃₄
    have hinnerIntersect : theta + theta < 1 := by
      nlinarith [hthetaLtSqrtDivSix, hsmall]
    obtain ⟨z, hz, hz₁₂, hz₃₄⟩ :=
      exists_and_of_almostEvery theta theta
        (D.fibre (D.index w + d₁ + d₂))
        (fun z => phi z - phi w = psi d₁ + psi d₂)
        (fun z => phi z - phi w = psi d₃ + psi d₄)
        hfinalNonempty hinnerIntersect hinner₁₂ hinner₃₄'
    exact hz₁₂.symm.trans hz₃₄

end LeanProofs.GowersSzemeredi
