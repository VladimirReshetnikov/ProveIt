import GowersSzemeredi.Proofs17FinitePatterns
import GowersSzemeredi.Proofs17Regions
import GowersSzemeredi.Proofs17PhaseRemoval
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Localized polynomial phase removal

This file proves Proposition 17.7.  The proof includes the balanced modular
interval partition and the sharper count of floor-affine patterns modulo
constant translations that are used in the localized argument.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Floor-affine patterns modulo translations -/

private def prop177ZeroVertex (k : Nat) : Fin k → Bool := fun _ => false

private def prop177SubsetSum {k : Nat} (a : Fin k → Real)
    (e : Fin k → Bool) : Real :=
  ∑ i, if e i then a i else 0

private def prop177NormalizedFloorPattern {k : Nat} (a0 : Real)
    (a : Fin k → Real) : (Fin k → Bool) → Int :=
  fun e => ⌊a0 + prop177SubsetSum a e⌋ - ⌊a0⌋

private def Prop177BoundedInt (R : Nat) :=
  ↑(Finset.Icc (-(R : Int)) (R : Int))

private abbrev Prop177BoundedPattern (k R : Nat) :=
  (Fin k → Bool) → Prop177BoundedInt R

private abbrev Prop177Threshold (k R : Nat) :=
  {e : Fin k → Bool // e ≠ prop177ZeroVertex k} ×
    ↑(Finset.Icc (-(R : Int) + 1) (R : Int))

private def prop177ThresholdCount (k R : Nat) : Nat :=
  Fintype.card (Prop177Threshold k R)

private def prop177ThresholdEquiv (k R : Nat) :
    Fin (prop177ThresholdCount k R) ≃ Prop177Threshold k R :=
  (Fintype.equivFin (Prop177Threshold k R)).symm

private def prop177ThresholdHyperplanes (k R : Nat) :
    Fin (prop177ThresholdCount k R) → AffineHyperplane (k + 2) :=
  fun i =>
    let q := prop177ThresholdEquiv k R i
    { normal := Fin.lastCases 1
        (Fin.lastCases 1 (fun j => if q.1.1 j then 1 else 0))
      offset := (q.2.1 : Real) }

private def prop177ThresholdCode {k R : Nat} (g : Prop177BoundedPattern k R) :
    Fin (prop177ThresholdCount k R) → Bool :=
  fun i => decide ((g (prop177ThresholdEquiv k R i).1.1).1 <
    (prop177ThresholdEquiv k R i).2.1)

private lemma prop177_realDot_threshold (k R : Nat)
    (q : Prop177Threshold k R) (t delta : Real) (a : Fin k → Real) :
    realDot
        (Fin.lastCases 1
          (Fin.lastCases 1 (fun j => if q.1.1 j then 1 else 0)))
        (Fin.lastCases delta (Fin.lastCases t a)) =
      prop177SubsetSum a q.1.1 + t + delta := by
  rw [realDot, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc, one_mul,
    prop177SubsetSum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  cases q.1.1 i <;> simp

private lemma prop177_exists_small_positive
    {I : Type*} [Fintype I] (y b : I → Real) :
    ∃ delta : Real, 0 < delta ∧ ∀ i, y i < b i → y i + delta < b i := by
  classical
  have haux : ∀ S : Finset I, ∃ delta : Real, 0 < delta ∧
      ∀ i, i ∈ S → y i < b i → y i + delta < b i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨1, by norm_num, by simp⟩
    | @insert i S hi ih =>
        obtain ⟨delta, hdelta, hdeltaS⟩ := ih
        by_cases hib : y i < b i
        · let eps : Real := (b i - y i) / 2
          have heps : 0 < eps := by dsimp only [eps]; linarith
          refine ⟨min delta eps, lt_min hdelta heps, ?_⟩
          intro j hj hyj
          rw [Finset.mem_insert] at hj
          rcases hj with hji | hj
          · subst j
            have hmin := min_le_right delta eps
            dsimp only [eps] at hmin ⊢
            linarith
          · have hprev := hdeltaS j hj hyj
            have hmin := min_le_left delta eps
            linarith
        · refine ⟨delta, hdelta, ?_⟩
          intro j hj hyj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact (hib hyj).elim
          · exact hdeltaS j hj hyj
  obtain ⟨delta, hdelta, hall⟩ := haux Finset.univ
  exact ⟨delta, hdelta, fun i => hall i (Finset.mem_univ i)⟩

private lemma prop177_floor_sub_floor_eq_fract (a s : Real) :
    ⌊a + s⌋ - ⌊a⌋ = ⌊Int.fract a + s⌋ := by
  have hfloor : ⌊a + s⌋ = ⌊a⌋ + ⌊Int.fract a + s⌋ := by
    calc
      ⌊a + s⌋ = ⌊((⌊a⌋ : Int) : Real) + Int.fract a + s⌋ := by
        congr 1
        rw [Int.floor_add_fract]
      _ = ⌊a⌋ + ⌊Int.fract a + s⌋ := by
        rw [add_assoc, Int.floor_intCast_add]
  omega

private lemma prop177_normalizedFloor_zero {k : Nat} (a0 : Real)
    (a : Fin k → Real) :
    prop177NormalizedFloorPattern a0 a (prop177ZeroVertex k) = 0 := by
  simp [prop177NormalizedFloorPattern, prop177SubsetSum, prop177ZeroVertex]

private lemma prop177_subsetSum_bounds {k : Nat} (hk : 0 < k)
    (a : Fin k → Real)
    (ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat))
    (e : Fin k → Bool) :
    -((k * (k + 1) : Nat) : Real) < prop177SubsetSum a e ∧
      prop177SubsetSum a e < (k * (k + 1) : Nat) := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  constructor
  · calc
      -((k * (k + 1) : Nat) : Real) =
          ∑ _i : Fin k, -((k + 1 : Nat) : Real) := by simp; ring
      _ < ∑ i : Fin k, (if e i then a i else 0) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        cases e i
        · simp only [Bool.false_eq_true, if_false]
          have hk1 : (0 : Real) < (k + 1 : Nat) := by
            exact_mod_cast Nat.succ_pos k
          exact neg_lt_zero.mpr hk1
        · simpa only [if_true] using (ha i).1
      _ = prop177SubsetSum a e := rfl
  · calc
      prop177SubsetSum a e =
          ∑ i : Fin k, (if e i then a i else 0) := rfl
      _ < ∑ _i : Fin k, ((k + 1 : Nat) : Real) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        cases e i
        · simp only [Bool.false_eq_true, if_false]
          exact_mod_cast Nat.succ_pos k
        · simpa only [if_true] using (ha i).2
      _ = ((k * (k + 1) : Nat) : Real) := by simp; ring

private lemma prop177_normalizedFloor_bounds {k : Nat} (hk : 0 < k)
    (a0 : Real) (a : Fin k → Real)
    (ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat))
    (e : Fin k → Bool) :
    -(k * (k + 1) : Int) ≤ prop177NormalizedFloorPattern a0 a e ∧
      prop177NormalizedFloorPattern a0 a e ≤ (k * (k + 1) : Int) := by
  rw [prop177NormalizedFloorPattern,
    prop177_floor_sub_floor_eq_fract]
  have hs := prop177_subsetSum_bounds hk a ha e
  have ht0 := Int.fract_nonneg a0
  have ht1 := Int.fract_lt_one a0
  constructor
  · rw [Int.le_floor]
    exact_mod_cast (le_of_lt (lt_of_lt_of_le hs.1 (by linarith)))
  · apply Int.floor_le_iff.mpr
    have hlt : Int.fract a0 + prop177SubsetSum a e <
        ((k * (k + 1) : Nat) : Real) + 1 := by linarith
    exact hlt

private def prop177BoundedPatternOf {k : Nat} (hk : 0 < k)
    (a0 : Real) (a : Fin k → Real)
    (ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)) :
    Prop177BoundedPattern k (k * (k + 1)) :=
  fun e => ⟨prop177NormalizedFloorPattern a0 a e, by
    simp only [Prop177BoundedInt, Finset.mem_Icc]
    change -(k * (k + 1) : Int) ≤ prop177NormalizedFloorPattern a0 a e ∧
      prop177NormalizedFloorPattern a0 a e ≤ (k * (k + 1) : Int)
    exact prop177_normalizedFloor_bounds hk a0 a ha e⟩

private lemma prop177_thresholdCode_realized {k : Nat} (hk : 0 < k)
    (a0 : Real) (a : Fin k → Real)
    (ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)) :
    RealizesRegion
      (prop177ThresholdHyperplanes k (k * (k + 1)))
      (prop177ThresholdCode (prop177BoundedPatternOf hk a0 a ha)) := by
  let t := Int.fract a0
  let y : Prop177Threshold k (k * (k + 1)) → Real :=
    fun q => prop177SubsetSum a q.1.1 + t
  let b : Prop177Threshold k (k * (k + 1)) → Real :=
    fun q => (q.2.1 : Real)
  obtain ⟨delta, hdelta, hsmall⟩ := prop177_exists_small_positive y b
  refine ⟨Fin.lastCases delta (Fin.lastCases t a), ?_⟩
  intro i
  let q := prop177ThresholdEquiv k (k * (k + 1)) i
  have hdot : realDot
      ((prop177ThresholdHyperplanes k (k * (k + 1))) i).normal
      (Fin.lastCases delta (Fin.lastCases t a)) = y q + delta := by
    simpa only [prop177ThresholdHyperplanes, q, y, t, add_assoc] using
      prop177_realDot_threshold k (k * (k + 1)) q t delta a
  have hfloor :
      (prop177BoundedPatternOf hk a0 a ha q.1.1).1 = ⌊y q⌋ := by
    simp only [prop177BoundedPatternOf, prop177NormalizedFloorPattern,
      prop177_floor_sub_floor_eq_fract, y, t]
    congr 1
    ac_rfl
  have hcode : prop177ThresholdCode (prop177BoundedPatternOf hk a0 a ha) i = true ↔
      y q < b q := by
    simp only [prop177ThresholdCode, q, decide_eq_true_eq, hfloor, b]
    exact Int.floor_lt
  constructor
  · rw [hcode, hdot]
    constructor
    · intro hy
      exact hsmall q hy
    · intro h
      exact (lt_add_of_pos_right _ hdelta).trans h
  · calc
      prop177ThresholdCode (prop177BoundedPatternOf hk a0 a ha) i = false ↔
          prop177ThresholdCode (prop177BoundedPatternOf hk a0 a ha) i ≠ true :=
        Bool.eq_false_iff
      _ ↔ ¬ y q < b q := not_congr hcode
      _ ↔ b q ≤ y q := not_lt
      _ ↔ b q < y q + delta := by
        constructor
        · intro h
          exact h.trans_lt (lt_add_of_pos_right _ hdelta)
        · intro h
          by_contra hnot
          have hy : y q < b q := lt_of_not_ge hnot
          exact (not_lt_of_ge h.le) (hsmall q hy)
      _ ↔ (prop177ThresholdHyperplanes k (k * (k + 1)) i).offset <
          realDot (prop177ThresholdHyperplanes k (k * (k + 1)) i).normal
            (Fin.lastCases delta (Fin.lastCases t a)) := by
        rw [hdot]
        rfl

private lemma prop177_thresholdCode_injective {k R : Nat} (_hR : 0 < R)
    {g h : Prop177BoundedPattern k R}
    (hg0 : (g (prop177ZeroVertex k)).1 = 0)
    (hh0 : (h (prop177ZeroVertex k)).1 = 0)
    (hcode : prop177ThresholdCode g = prop177ThresholdCode h) : g = h := by
  funext e
  apply Subtype.ext
  by_cases he0 : e = prop177ZeroVertex k
  · subst e
    exact hg0.trans hh0.symm
  · apply le_antisymm
    · by_contra hle
      have hlt : h e < g e := lt_of_not_ge hle
      have hltInt : (h e).1 < (g e).1 := by exact_mod_cast hlt
      let j : Int := (g e).1
      have hj : j ∈ Finset.Icc (-(R : Int) + 1) (R : Int) := by
        have hg : -(R : Int) ≤ (g e).1 ∧ (g e).1 ≤ (R : Int) := by
          simpa only [Prop177BoundedInt, Finset.mem_Icc] using (g e).2
        have hh : -(R : Int) ≤ (h e).1 ∧ (h e).1 ≤ (R : Int) := by
          simpa only [Prop177BoundedInt, Finset.mem_Icc] using (h e).2
        simp only [Finset.mem_Icc]
        exact ⟨Int.add_one_le_iff.mpr (hh.1.trans_lt hltInt), hg.2⟩
      let q : Prop177Threshold k R := ⟨⟨e, he0⟩, ⟨j, hj⟩⟩
      let i : Fin (prop177ThresholdCount k R) :=
        (prop177ThresholdEquiv k R).symm q
      have hiq : prop177ThresholdEquiv k R i = q := by simp [i]
      have hc := congrFun hcode i
      simp only [prop177ThresholdCode, hiq, q, j, decide_eq_decide] at hc
      simp [hltInt] at hc
    · by_contra hle
      have hlt : g e < h e := lt_of_not_ge hle
      have hltInt : (g e).1 < (h e).1 := by exact_mod_cast hlt
      let j : Int := (h e).1
      have hj : j ∈ Finset.Icc (-(R : Int) + 1) (R : Int) := by
        have hh : -(R : Int) ≤ (h e).1 ∧ (h e).1 ≤ (R : Int) := by
          simpa only [Prop177BoundedInt, Finset.mem_Icc] using (h e).2
        have hg : -(R : Int) ≤ (g e).1 ∧ (g e).1 ≤ (R : Int) := by
          simpa only [Prop177BoundedInt, Finset.mem_Icc] using (g e).2
        simp only [Finset.mem_Icc]
        exact ⟨Int.add_one_le_iff.mpr (hg.1.trans_lt hltInt), hh.2⟩
      let q : Prop177Threshold k R := ⟨⟨e, he0⟩, ⟨j, hj⟩⟩
      let i : Fin (prop177ThresholdCount k R) :=
        (prop177ThresholdEquiv k R).symm q
      have hiq : prop177ThresholdEquiv k R i = q := by simp [i]
      have hc := congrFun hcode i
      simp only [prop177ThresholdCode, hiq, q, j, decide_eq_decide] at hc
      simp [hltInt] at hc

private lemma prop177_thresholdCount_eq (k R : Nat) :
    prop177ThresholdCount k R = (2 ^ k - 1) * (2 * R) := by
  classical
  simp only [prop177ThresholdCount, Prop177Threshold, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unique]
  congr 1
  rw [Fintype.card_coe, Int.card_Icc]
  omega

private lemma prop177_sum_range_pow_le_two_mul_pow (n d : Nat) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (d + 1), n ^ j) ≤ 2 * n ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hstep : 2 * n ^ d ≤ n ^ (d + 1) := by
        rw [pow_succ]
        simpa only [mul_comm] using Nat.mul_le_mul_right (n ^ d) hn
      calc
        (∑ j ∈ Finset.range (d + 1), n ^ j) + n ^ (d + 1) ≤
            2 * n ^ d + n ^ (d + 1) := Nat.add_le_add_right ih _
        _ ≤ n ^ (d + 1) + n ^ (d + 1) := Nat.add_le_add_right hstep _
        _ = 2 * n ^ (d + 1) := by omega

private lemma prop177_two_mul_k_succ_le_pow (k : Nat) :
    2 * k * (k + 1) ≤ 2 ^ (2 * k + 2) := by
  have hk : k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
  have hks : k + 1 ≤ 2 ^ (k + 1) := Nat.le_of_lt (k + 1).lt_two_pow_self
  calc
    2 * k * (k + 1) ≤ 2 * 2 ^ k * 2 ^ (k + 1) := by gcongr
    _ = 2 ^ (k + 1) * 2 ^ (k + 1) := by
      rw [pow_succ]
      ring
    _ = 2 ^ ((k + 1) + (k + 1)) :=
      (pow_add 2 (k + 1) (k + 1)).symm
    _ = 2 ^ (2 * k + 2) := by
      congr 1
      omega

private lemma prop177_thresholdCount_le_pow (k : Nat) :
    prop177ThresholdCount k (k * (k + 1)) ≤ 2 ^ (3 * k + 2) := by
  rw [prop177_thresholdCount_eq]
  calc
    (2 ^ k - 1) * (2 * (k * (k + 1))) ≤
        2 ^ k * 2 ^ (2 * k + 2) := by
      apply Nat.mul_le_mul
      · exact Nat.sub_le _ _
      · simpa [mul_assoc] using prop177_two_mul_k_succ_le_pow k
    _ = 2 ^ (3 * k + 2) := by
      rw [← pow_add]
      congr 1
      omega

private lemma prop177_region_sum_bound (k : Nat) (hk : 0 < k) :
    (∑ j ∈ Finset.range (k + 3),
        Nat.choose (prop177ThresholdCount k (k * (k + 1))) j) ≤
      2 ^ (k * (k + 1) ^ 2) := by
  let n := prop177ThresholdCount k (k * (k + 1))
  by_cases hk4 : 4 ≤ k
  · have hn2 : 2 ≤ n := by
      dsimp only [n]
      rw [prop177_thresholdCount_eq]
      have hpow : 2 ≤ 2 ^ k := by
        exact (show 2 ^ 1 ≤ 2 ^ k from Nat.pow_le_pow_right (by decide) hk)
      have hR : 0 < k * (k + 1) := Nat.mul_pos hk (Nat.succ_pos k)
      have hfirst : 1 ≤ 2 ^ k - 1 := by omega
      have hsecond : 2 ≤ 2 * (k * (k + 1)) := by omega
      exact (show 2 = 1 * 2 by norm_num) ▸ Nat.mul_le_mul hfirst hsecond
    have hn : n ≤ 2 ^ (3 * k + 2) := prop177_thresholdCount_le_pow k
    calc
      (∑ j ∈ Finset.range (k + 3), Nat.choose n j) ≤
          ∑ j ∈ Finset.range (k + 3), n ^ j := by
        exact Finset.sum_le_sum fun j _ => Nat.choose_le_pow _ _
      _ ≤ 2 * n ^ (k + 2) := by
        simpa only [Nat.add_assoc] using
          prop177_sum_range_pow_le_two_mul_pow n (k + 2) hn2
      _ ≤ 2 * (2 ^ (3 * k + 2)) ^ (k + 2) := by
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn _)
      _ = 2 ^ 1 * 2 ^ ((3 * k + 2) * (k + 2)) := by
        rw [pow_mul]
        norm_num
      _ = 2 ^ (1 + (3 * k + 2) * (k + 2)) := by rw [pow_add]
      _ ≤ 2 ^ (k * (k + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith
  · interval_cases k <;>
      norm_num [n, prop177_thresholdCount_eq, Finset.sum_range_succ] <;>
      (set_option maxRecDepth 100000 in decide)

private def prop177RealizablePattern {k : Nat} (hk : 0 < k)
    (g : Prop177BoundedPattern k (k * (k + 1))) : Prop :=
  (g (prop177ZeroVertex k)).1 = 0 ∧
    ∃ (a0 : Real) (a : Fin k → Real)
      (ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)),
      g = prop177BoundedPatternOf hk a0 a ha

private theorem prop177_exists_normalized_integer_patterns (k : Nat) (hk : 0 < k) :
    ∃ F : Finset ((Fin k → Bool) → Int),
      F.card ≤ 2 ^ (k * (k + 1) ^ 2) ∧
      (∀ g, g ∈ F → g (prop177ZeroVertex k) = 0) ∧
      ∀ (a0 : Real) (a : Fin k → Real),
        (∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)) →
        prop177NormalizedFloorPattern a0 a ∈ F := by
  classical
  let R := k * (k + 1)
  let S : Finset (Prop177BoundedPattern k R) :=
    Finset.univ.filter (prop177RealizablePattern hk)
  let unbox : Prop177BoundedPattern k R → ((Fin k → Bool) → Int) :=
    fun g e => (g e).1
  let F := S.image unbox
  refine ⟨F, ?_, ?_, ?_⟩
  · let C := S.image prop177ThresholdCode
    have hcodeInj : ∀ ⦃g⦄, g ∈ S → ∀ ⦃h⦄, h ∈ S →
        prop177ThresholdCode g = prop177ThresholdCode h → g = h := by
      intro g hg h hh hcode
      have hg' := (Finset.mem_filter.mp hg).2.1
      have hh' := (Finset.mem_filter.mp hh).2.1
      exact prop177_thresholdCode_injective
        (Nat.mul_pos hk (Nat.succ_pos k)) hg' hh' hcode
    have hCcard : C.card = S.card := by
      exact Finset.card_image_iff.mpr hcodeInj
    have hCsubset : C ⊆ Finset.univ.filter
        (RealizesRegion (prop177ThresholdHyperplanes k R)) := by
      intro p hp
      simp only [C, Finset.mem_image] at hp
      obtain ⟨g, hgS, rfl⟩ := hp
      simp only [S, Finset.mem_filter] at hgS
      obtain ⟨hg0, a0, a, ha, rfl⟩ := hgS.2
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, prop177_thresholdCode_realized hk a0 a ha⟩
    have hregions : S.card ≤ hyperplaneRegionCount
        (prop177ThresholdHyperplanes k R) := by
      rw [← hCcard]
      unfold hyperplaneRegionCount countWhere
      exact Finset.card_le_card hCsubset
    have harrange := (lemma_17_4_holds (k + 2)
      (prop177ThresholdCount k R) (prop177ThresholdHyperplanes k R)).1
    calc
      F.card ≤ S.card := Finset.card_image_le
      _ ≤ hyperplaneRegionCount (prop177ThresholdHyperplanes k R) := hregions
      _ ≤ ∑ j ∈ Finset.range (k + 3),
          Nat.choose (prop177ThresholdCount k R) j := by
        simpa only [Nat.add_assoc] using harrange
      _ ≤ 2 ^ (k * (k + 1) ^ 2) := prop177_region_sum_bound k hk
  · intro g hg
    simp only [F, Finset.mem_image] at hg
    obtain ⟨g', hgS, rfl⟩ := hg
    exact (Finset.mem_filter.mp hgS).2.1
  · intro a0 a ha
    let g := prop177BoundedPatternOf hk a0 a ha
    have hgS : g ∈ S := by
      simp only [S, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, a0, a, ha, rfl⟩
      simpa only [g, prop177BoundedPatternOf] using
        prop177_normalizedFloor_zero a0 a
    simp only [F, Finset.mem_image]
    refine ⟨g, hgS, ?_⟩
    funext e
    rfl

private theorem prop177_exists_normalized_mod_patterns (k M : Nat)
    (hk : 0 < k) :
    ∃ F : Finset ((Fin k → Bool) → ZMod M),
      F.card ≤ 2 ^ (k * (k + 1) ^ 2) ∧
      (∀ g, g ∈ F → g (prop177ZeroVertex k) = 0) ∧
      ∀ (a0 : Real) (a : Fin k → Real),
        (∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)) →
        (fun e => floorAffinePattern (M := M) a0 a e -
          floorAffinePattern (M := M) a0 a (prop177ZeroVertex k)) ∈ F := by
  classical
  obtain ⟨G, hGcard, hGzero, hGmem⟩ :=
    prop177_exists_normalized_integer_patterns k hk
  let castPattern : ((Fin k → Bool) → Int) → ((Fin k → Bool) → ZMod M) :=
    fun g e => (g e : ZMod M)
  let F := G.image castPattern
  refine ⟨F, Finset.card_image_le.trans hGcard, ?_, ?_⟩
  · intro g hg
    simp only [F, Finset.mem_image] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simp only [castPattern]
    rw [hGzero g' hg']
    exact Int.cast_zero
  · intro a0 a ha
    have hg := hGmem a0 a ha
    simp only [F, Finset.mem_image]
    refine ⟨prop177NormalizedFloorPattern a0 a, hg, ?_⟩
    funext e
    simp only [castPattern, prop177NormalizedFloorPattern, floorAffinePattern,
      prop177SubsetSum, prop177ZeroVertex, Bool.false_eq_true, if_false,
      Finset.sum_const_zero, add_zero, Int.cast_sub]

/-! ### Balanced modular interval partitions -/

private def prop177CellWidth (N M : Nat) : Real := (N : Real) / M

private def prop177Boundary (N M i : Nat) : Nat :=
  Nat.ceil ((i : Real) * prop177CellWidth N M)

private def prop177BalancedCell (N M : Nat) (i : Fin M) : ModAP N :=
  modInterval N (prop177Boundary N M i : ZMod N)
    (prop177Boundary N M (i + 1) - prop177Boundary N M i)

private lemma prop177_width_pos {N M : Nat} (hN : 0 < N) (hM : 0 < M) :
    0 < prop177CellWidth N M := by
  unfold prop177CellWidth
  positivity

private lemma prop177_boundary_zero (N M : Nat) :
    prop177Boundary N M 0 = 0 := by
  simp [prop177Boundary, prop177CellWidth]

private lemma prop177_boundary_end {N M : Nat} (hM : 0 < M) :
    prop177Boundary N M M = N := by
  unfold prop177Boundary prop177CellWidth
  have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM.ne'
  have heq : (M : Real) * ((N : Real) / M) = N := by field_simp
  rw [heq]
  exact Nat.ceil_natCast N

private lemma prop177_boundary_mono {N M : Nat}
    (hN : 0 < N) (hM : 0 < M) : Monotone (prop177Boundary N M) := by
  intro i j hij
  unfold prop177Boundary
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (prop177_width_pos hN hM).le

private lemma prop177_boundary_le_N {N M i : Nat}
    (hN : 0 < N) (hM : 0 < M) (hi : i ≤ M) :
    prop177Boundary N M i ≤ N := by
  calc
    prop177Boundary N M i ≤ prop177Boundary N M M :=
      prop177_boundary_mono hN hM hi
    _ = N := prop177_boundary_end hM

private lemma prop177_modInterval_mem_iff_val {N b L : Nat} [NeZero N]
    (hend : b + L ≤ N) (x : ZMod N) :
    x ∈ (modInterval N (b : ZMod N) L).carrier ↔
      b ≤ x.val ∧ x.val < b + L := by
  classical
  rw [modInterval, ModAP.carrier]
  simp only [mul_one, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have hlt : b + (i : Nat) < N := lt_of_lt_of_le (Nat.add_lt_add_left i.isLt b) hend
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt hlt]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt b⟩
  · rintro ⟨hbx, hxe⟩
    let j : Fin L := ⟨x.val - b, by omega⟩
    refine ⟨j, ?_⟩
    rw [← Nat.cast_add, show b + (j : Nat) = x.val by dsimp only [j]; omega,
      ZMod.natCast_zmod_val]

private lemma prop177_balancedCell_mem_iff {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) (x : ZMod N) :
    x ∈ (prop177BalancedCell N M i).carrier ↔
      prop177Boundary N M i ≤ x.val ∧
        x.val < prop177Boundary N M (i + 1) := by
  have hN : 0 < N := NeZero.pos N
  have hmono := prop177_boundary_mono hN hM (Nat.le_succ i)
  have hend : prop177Boundary N M i +
      (prop177Boundary N M (i + 1) - prop177Boundary N M i) ≤ N := by
    rw [Nat.add_sub_of_le hmono]
    exact prop177_boundary_le_N hN hM (Nat.succ_le_iff.mpr i.isLt)
  rw [prop177BalancedCell, prop177_modInterval_mem_iff_val hend]
  rw [Nat.add_sub_of_le hmono]

private def prop177CellIndex {N M : Nat} [NeZero N]
    (hM : 0 < M) (x : ZMod N) : Fin M :=
  ⟨Nat.floor ((x.val : Real) / prop177CellWidth N M), by
    apply (Nat.floor_lt' hM.ne').mpr
    rw [div_lt_iff₀ (prop177_width_pos (NeZero.pos N) hM)]
    have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM.ne'
    have heq : (M : Real) * prop177CellWidth N M = N := by
      unfold prop177CellWidth
      field_simp
    rw [heq]
    exact_mod_cast ZMod.val_lt x⟩

private lemma prop177_cellIndex_spec {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) (x : ZMod N) :
    prop177CellIndex hM x = i ↔
      prop177Boundary N M i ≤ x.val ∧
        x.val < prop177Boundary N M (i + 1) := by
  have hw : 0 < prop177CellWidth N M := prop177_width_pos (NeZero.pos N) hM
  have hx0 : 0 ≤ (x.val : Real) / prop177CellWidth N M := by positivity
  rw [Fin.ext_iff]
  change Nat.floor ((x.val : Real) / prop177CellWidth N M) = (i : Nat) ↔
    Nat.ceil ((i : Real) * prop177CellWidth N M) ≤ x.val ∧
      x.val < Nat.ceil ((((i : Nat) + 1 : Nat) : Real) * prop177CellWidth N M)
  rw [Nat.floor_eq_iff hx0]
  constructor
  · rintro ⟨hiL, hiU⟩
    constructor
    · apply Nat.ceil_le.mpr
      exact (le_div_iff₀ hw).mp hiL
    · apply Nat.lt_ceil.mpr
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact (div_lt_iff₀ hw).mp hiU
  · rintro ⟨hiL, hiU⟩
    constructor
    · apply (le_div_iff₀ hw).mpr
      exact Nat.ceil_le.mp hiL
    · apply (div_lt_iff₀ hw).mpr
      have h := Nat.lt_ceil.mp hiU
      norm_num only [Nat.cast_add, Nat.cast_one] at h
      exact h

private lemma prop177_balancedCell_mem_iff_index {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) (x : ZMod N) :
    x ∈ (prop177BalancedCell N M i).carrier ↔ prop177CellIndex hM x = i := by
  rw [prop177_balancedCell_mem_iff hM, prop177_cellIndex_spec]

private lemma prop177_balancedCell_partition {N M : Nat} [NeZero N]
    (hM : 0 < M) :
    IsPartition (fun i : Fin M => (prop177BalancedCell N M i).carrier)
      Finset.univ := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_univ, true_iff]
    exact ⟨prop177CellIndex hM x,
      (prop177_balancedCell_mem_iff_index hM _ _).mpr rfl⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi := (prop177_balancedCell_mem_iff_index hM i x).mp hxi
    have hj := (prop177_balancedCell_mem_iff_index hM j x).mp hxj
    exact bne_iff_ne.mp hij (hi.symm.trans hj)

private lemma prop177_balancedCell_isProper {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) : (prop177BalancedCell N M i).IsProper := by
  classical
  let b := prop177Boundary N M i
  let L := prop177Boundary N M (i + 1) - b
  have hmono : prop177Boundary N M i ≤ prop177Boundary N M (i + 1) :=
    prop177_boundary_mono (NeZero.pos N) hM (Nat.le_succ i)
  have hend : b + L ≤ N := by
    rw [show b + L = prop177Boundary N M (i + 1) by
      dsimp only [b, L]; omega]
    exact prop177_boundary_le_N (NeZero.pos N) hM (Nat.succ_le_iff.mpr i.isLt)
  have hinj : Function.Injective (fun j : Fin L => (b : ZMod N) + (j : Nat)) := by
    intro a b' hab
    have haN : b + (a : Nat) < N := lt_of_lt_of_le
      (Nat.add_lt_add_left a.isLt b) hend
    have hbN : b + (b' : Nat) < N := lt_of_lt_of_le
      (Nat.add_lt_add_left b'.isLt b) hend
    have := congrArg ZMod.val hab
    have hsum : b + (a : Nat) = b + (b' : Nat) := by
      simpa only [← Nat.cast_add, ZMod.val_natCast_of_lt haN,
        ZMod.val_natCast_of_lt hbN] using this
    exact Fin.ext (Nat.add_left_cancel hsum)
  unfold prop177BalancedCell ModAP.IsProper modInterval ModAP.carrier
  simp only [mul_one]
  rw [Finset.card_image_iff.mpr (by simpa only [b, L] using hinj.injOn),
    Finset.card_univ, Fintype.card_fin]

private lemma prop177_boundary_increment {N M q : Nat}
    (hN : 0 < N) (hM : 0 < M)
    (hqW : (q : Real) ≤ prop177CellWidth N M)
    (hWq : prop177CellWidth N M < q + 1)
    (i : Fin M) :
    prop177Boundary N M (i + 1) - prop177Boundary N M i = q ∨
      prop177Boundary N M (i + 1) - prop177Boundary N M i = q + 1 := by
  let w := prop177CellWidth N M
  have hw0 : 0 ≤ w := (prop177_width_pos hN hM).le
  have hiw0 : 0 ≤ (i : Real) * w := mul_nonneg (by positivity) hw0
  have hmono := prop177_boundary_mono hN hM (Nat.le_succ i)
  have hlower : prop177Boundary N M i + q ≤ prop177Boundary N M (i + 1) := by
    rw [prop177Boundary, prop177Boundary]
    rw [← Nat.ceil_add_natCast hiw0]
    apply Nat.ceil_mono
    dsimp only [w]
    push_cast
    nlinarith
  have hupper : prop177Boundary N M (i + 1) ≤ prop177Boundary N M i + q + 1 := by
    simp only [prop177Boundary]
    apply Nat.ceil_le.mpr
    have hceil := Nat.le_ceil ((i : Real) * prop177CellWidth N M)
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have : q ≤ prop177Boundary N M (i + 1) - prop177Boundary N M i ∧
      prop177Boundary N M (i + 1) - prop177Boundary N M i ≤ q + 1 := by
    omega
  omega

private lemma prop177_cellIndex_intCast {N M : Nat} [NeZero N]
    (hM : 0 < M) (z : Int) :
    (((prop177CellIndex (N := N) hM (z : ZMod N) : Fin M) : Nat) : ZMod M) =
      (⌊(z : Real) / prop177CellWidth N M⌋ : ZMod M) := by
  have hN : 0 < N := NeZero.pos N
  have hw : 0 < prop177CellWidth N M := prop177_width_pos hN hM
  have hrem : 0 ≤ z % (N : Int) :=
    Int.emod_nonneg z (by exact_mod_cast hN.ne')
  have hval : (((z : ZMod N).val : Nat) : Real) =
      ((z % (N : Int) : Int) : Real) := by
    exact_mod_cast ZMod.val_intCast z
  have hdecomp :
      (z : Real) / prop177CellWidth N M =
        ((z % (N : Int) : Int) : Real) / prop177CellWidth N M +
          (((M : Int) * (z / (N : Int)) : Int) : Real) := by
    have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM.ne'
    have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
    have hz := Int.emod_add_mul_ediv z (N : Int)
    have hzR : (z : Real) =
        ((z % (N : Int) : Int) : Real) +
          (N : Real) * ((z / (N : Int) : Int) : Real) := by
      exact_mod_cast hz.symm
    unfold prop177CellWidth
    rw [hzR]
    field_simp
    push_cast
    ring
  change ((Nat.floor ((((z : ZMod N).val : Nat) : Real) /
      prop177CellWidth N M) : Nat) : ZMod M) = _
  rw [hval]
  have hnonneg : 0 ≤ ((z % (N : Int) : Int) : Real) /
      prop177CellWidth N M := div_nonneg (by exact_mod_cast hrem) hw.le
  calc
    ((Nat.floor (((z % (N : Int) : Int) : Real) /
        prop177CellWidth N M) : Nat) : ZMod M) =
        (((Nat.floor (((z % (N : Int) : Int) : Real) /
          prop177CellWidth N M) : Nat) : Int) : ZMod M) := by norm_num
    _ = (⌊((z % (N : Int) : Int) : Real) /
        prop177CellWidth N M⌋ : ZMod M) := by
      rw [Int.natCast_floor_eq_floor hnonneg]
    _ = (⌊(z : Real) / prop177CellWidth N M⌋ : ZMod M) := by
      rw [hdecomp, Int.floor_add_intCast]
      push_cast
      simp

private lemma prop177_cellIndex_floorAffine {N M k : Nat} [NeZero N]
    (hM : 0 < M) (t : ZMod N) (a : Fin k → Int)
    (e : Fin k → Bool) :
    (((prop177CellIndex (N := N) hM
        (t - ∑ i, if e i then (a i : ZMod N) else 0) : Fin M) : Nat) :
        ZMod M) =
      floorAffinePattern (M := M)
        ((t.val : Real) / prop177CellWidth N M)
        (fun i => -((a i : Int) : Real) / prop177CellWidth N M) e := by
  let z : Int := (t.val : Int) - ∑ i, if e i then a i else 0
  have hzmod : (z : ZMod N) =
      t - ∑ i, if e i then (a i : ZMod N) else 0 := by
    dsimp only [z]
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hzmod, prop177_cellIndex_intCast hM z]
  unfold floorAffinePattern
  congr 1
  dsimp only [z]
  push_cast
  rw [sub_div, Finset.sum_div, sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib]
  congr 1
  rw [add_left_cancel_iff]
  apply Finset.sum_congr rfl
  intro i _
  cases e i <;> simp [neg_div]

private def prop177FinZModEquiv (N : Nat) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i : ZMod N)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv i := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv x := ZMod.natCast_zmod_val x

private def prop177ResidueCell (N M : Nat) [NeZero M]
    (j : ZMod M) : ModAP N :=
  prop177BalancedCell N M ((prop177FinZModEquiv M).symm j)

private lemma prop177_mem_residueCell_iff {N M : Nat} [NeZero N]
    [NeZero M] (hM : 0 < M) (j : ZMod M) (x : ZMod N) :
    x ∈ (prop177ResidueCell N M j).carrier ↔
      ((((prop177CellIndex (N := N) hM x : Fin M) : Nat) : ZMod M) = j) := by
  rw [prop177ResidueCell, prop177_balancedCell_mem_iff_index hM]
  exact (prop177FinZModEquiv M).apply_eq_iff_eq_symm_apply.symm

private def prop177RawPattern {N M k : Nat} [NeZero N]
    (hM : 0 < M) (t : ZMod N) (a : Fin k → Int) :
    (Fin k → Bool) → ZMod M :=
  fun e => (((prop177CellIndex (N := N) hM
    (t - ∑ i, if e i then (a i : ZMod N) else 0) : Fin M) : Nat) : ZMod M)

private lemma prop177_normalized_raw_mem {N M k : Nat} [NeZero N]
    (hM : 0 < M)
    (F : Finset ((Fin k → Bool) → ZMod M))
    (hFmem : ∀ (a0 : Real) (a : Fin k → Real),
      (∀ i, -((k + 1 : Nat) : Real) < a i ∧
        a i < (k + 1 : Nat)) →
      (fun e => floorAffinePattern (M := M) a0 a e -
        floorAffinePattern (M := M) a0 a (prop177ZeroVertex k)) ∈ F)
    (t : ZMod N) (a : Fin k → Int)
    (ha : ∀ i,
      -((k + 1 : Nat) : Real) <
          -((a i : Int) : Real) / prop177CellWidth N M ∧
      -((a i : Int) : Real) / prop177CellWidth N M <
          (k + 1 : Nat)) :
    (fun e => prop177RawPattern hM t a e -
      prop177RawPattern hM t a (prop177ZeroVertex k)) ∈ F := by
  have hfloor (e : Fin k → Bool) :
      prop177RawPattern hM t a e =
        floorAffinePattern (M := M)
          ((t.val : Real) / prop177CellWidth N M)
          (fun i => -((a i : Int) : Real) / prop177CellWidth N M) e := by
    exact prop177_cellIndex_floorAffine hM t a e
  simpa only [hfloor] using hFmem
    ((t.val : Real) / prop177CellWidth N M)
    (fun i => -((a i : Int) : Real) / prop177CellWidth N M) ha

private lemma prop177_support_decomposition {N M k : Nat} [NeZero N]
    [NeZero M] (hM : 0 < M)
    (F : Finset ((Fin k → Bool) → ZMod M))
    (hFzero : ∀ g, g ∈ F → g (prop177ZeroVertex k) = 0)
    (H : (Fin k → Bool) → ZMod N → Complex)
    (t : ZMod N) (a : Fin k → Int)
    (hnorm : (fun e => prop177RawPattern hM t a e -
      prop177RawPattern hM t a (prop177ZeroVertex k)) ∈ F) :
    (∏ e : Fin k → Bool,
      parityConj e
        (H e (t - ∑ i, if e i then (a i : ZMod N) else 0))) =
      ∑ g ∈ F, ∑ c : ZMod M,
        ∏ e : Fin k → Bool,
          parityConj e
            (restrictToCell
              (prop177ResidueCell N M (g e + c)).carrier (H e)
              (t - ∑ i, if e i then (a i : ZMod N) else 0)) := by
  classical
  let e0 := prop177ZeroVertex k
  let p := prop177RawPattern hM t a
  let g0 : (Fin k → Bool) → ZMod M := fun e => p e - p e0
  let c0 : ZMod M := p e0
  have hg0 : g0 ∈ F := hnorm
  rw [Finset.sum_eq_single g0]
  · rw [Finset.sum_eq_single c0]
    · apply Finset.prod_congr rfl
      intro e _
      have hcell :
          (t - ∑ i, if e i then (a i : ZMod N) else 0) ∈
            (prop177ResidueCell N M (g0 e + c0)).carrier := by
        rw [prop177_mem_residueCell_iff hM]
        dsimp only [p, g0, c0, prop177RawPattern]
        ring
      unfold restrictToCell
      rw [if_pos hcell]
    · intro c _ hc
      apply Finset.prod_eq_zero (Finset.mem_univ e0)
      have hnot :
          (t - ∑ i, if e0 i then (a i : ZMod N) else 0) ∉
            (prop177ResidueCell N M (g0 e0 + c)).carrier := by
        rw [prop177_mem_residueCell_iff hM]
        dsimp only [g0, c0]
        simp only [sub_self, zero_add]
        exact fun h => hc (by
          simpa only [c0, p, prop177RawPattern] using h.symm)
      unfold restrictToCell
      rw [if_neg hnot]
      simp [parityConj]
    · simp
  · intro g hgF hgne
    rw [Finset.sum_eq_zero]
    intro c _
    have hex : ∃ e : Fin k → Bool, p e ≠ g e + c := by
      by_contra h
      push Not at h
      have hc : c = p e0 := by
        have := h e0
        rw [hFzero g hgF] at this
        simpa only [zero_add] using this.symm
      apply hgne
      funext e
      have he := h e
      rw [hc] at he
      dsimp only [g0]
      exact eq_sub_of_add_eq he.symm
    obtain ⟨e, he⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    have hnot :
        (t - ∑ i, if e i then (a i : ZMod N) else 0) ∉
          (prop177ResidueCell N M (g e + c)).carrier := by
      rw [prop177_mem_residueCell_iff hM]
      exact he
    unfold restrictToCell
    rw [if_neg hnot]
    simp [parityConj]
  · intro h
    exact (h hg0).elim

/-! ### The small-scale singleton branch -/

private lemma prop177_cubeArgument_cons {N n : Nat}
    (s r : ZMod N) (a : Point N n) (b : Bool) (e : Fin n → Bool) :
    cubeArgument s (Fin.cons r a) (Fin.cons b e) =
      s - (if b then r else 0) - ∑ i, if e i then a i else 0 := by
  unfold cubeArgument
  rw [Fin.sum_univ_succ]
  simp
  abel

private lemma prop177_norm_cubeDifference_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    ‖cubeDifference f x s‖ =
      ∏ e : Fin d → Bool, ‖f (cubeArgument s x e)‖ := by
  induction d generalizing s with
  | zero =>
      simp [cubeDifference, iteratedDifference, cubeArgument]
  | succ n ih =>
      let r : ZMod N := x 0
      let a : Point N n := Fin.tail x
      have hx : x = Fin.cons r a := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hx, cubeDifference_cons]
      simp only [difference, norm_mul, norm_star, ih]
      let T : (Fin (n + 1) → Bool) → Real := fun e =>
        ‖f (cubeArgument s (Fin.cons r a) e)‖
      calc
        (∏ e : Fin n → Bool, ‖f (cubeArgument s a e)‖) *
            ∏ e : Fin n → Bool, ‖f (cubeArgument (s - r) a e)‖ =
            (∏ e : Fin n → Bool, T (Fin.cons false e)) *
              ∏ e : Fin n → Bool, T (Fin.cons true e) := by
          congr 1
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T, prop177_cubeArgument_cons, Bool.false_eq_true, if_false,
              sub_zero]
            rfl
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T, prop177_cubeArgument_cons, if_true]
            rfl
        _ = ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
        _ = ∏ e : Fin (n + 1) → Bool, T e := by
          exact (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).prod_comp T

private lemma prop177_cube_norm_sq_le_moment {N k : Nat}
    (f : ZMod N → Complex) (x : Point N k) (s : ZMod N) :
    ‖cubeDifference f x s‖ ^ 2 ≤
      ((2 : Real) ^ k)⁻¹ *
        ∑ e : Fin k → Bool, ‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1)) := by
  let n : Nat := 2 ^ k
  let p : Nat := 2 ^ (k + 1)
  let w : Real := (n : Real)⁻¹
  let G : (Fin k → Bool) → Real := fun e =>
    ‖f (cubeArgument s x e)‖ ^ p
  have hn : 0 < (n : Real) := by positivity
  have hw : 0 < w := inv_pos.mpr hn
  have hweight : ∑ _e : Fin k → Bool, w = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    change (n : Real) * w = 1
    exact mul_inv_cancel₀ hn.ne'
  have hG : ∀ e, 0 ≤ G e := fun e => pow_nonneg (norm_nonneg _) _
  have hpw : (p : Real) * w = 2 := by
    dsimp only [p, w, n]
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hterm (e : Fin k → Bool) : G e ^ w = ‖f (cubeArgument s x e)‖ ^ 2 := by
    dsimp only [G]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (norm_nonneg _)]
    rw [hpw, Real.rpow_two]
  calc
    ‖cubeDifference f x s‖ ^ 2 =
        ∏ e : Fin k → Bool, ‖f (cubeArgument s x e)‖ ^ 2 := by
      rw [prop177_norm_cubeDifference_product, Finset.prod_pow]
    _ = ∏ e : Fin k → Bool, G e ^ w := by
      apply Finset.prod_congr rfl
      intro e _
      exact (hterm e).symm
    _ ≤ ∑ e : Fin k → Bool, w * G e :=
      Real.geom_mean_le_arith_mean_weighted Finset.univ
        (fun _ => w) G (fun _ _ => hw.le) hweight (fun e _ => hG e)
    _ = ((2 : Real) ^ k)⁻¹ *
        ∑ e : Fin k → Bool, ‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1)) := by
      rw [← Finset.mul_sum]
      simp only [w, n, G, p, Nat.cast_pow, Nat.cast_ofNat]

private lemma prop177_sum_cube_norm_sq_le_moment {N k : Nat} [NeZero N]
    (f : ZMod N → Complex) (x : Point N k) :
    ∑ s : ZMod N, ‖cubeDifference f x s‖ ^ 2 ≤
      ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := by
  let T : Real := ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1))
  calc
    (∑ s : ZMod N, ‖cubeDifference f x s‖ ^ 2) ≤
        ∑ s : ZMod N, ((2 : Real) ^ k)⁻¹ *
          ∑ e : Fin k → Bool,
            ‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1)) := by
      exact Finset.sum_le_sum fun s _ => prop177_cube_norm_sq_le_moment f x s
    _ = ((2 : Real) ^ k)⁻¹ *
        ∑ e : Fin k → Bool, ∑ s : ZMod N,
            ‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = ((2 : Real) ^ k)⁻¹ * ∑ _e : Fin k → Bool, T := by
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      let c : ZMod N := ∑ i, if e i then x i else 0
      change (∑ s : ZMod N, ‖f (s - c)‖ ^ ((2 : Nat) ^ (k + 1))) = T
      exact (Equiv.subRight c).sum_comp
        (fun s : ZMod N => ‖f s‖ ^ ((2 : Nat) ^ (k + 1)))
    _ = T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      field_simp
    _ = ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := rfl

private lemma prop177_fourier_sq_le_moment {N k : Nat} [NeZero N]
    (f : ZMod N → Complex) (x : Point N k) (r : ZMod N) :
    ‖fourier (cubeDifference f x) r‖ ^ 2 ≤
      (N : Real) * ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := by
  calc
    ‖fourier (cubeDifference f x) r‖ ^ 2 ≤
        ∑ u : ZMod N, ‖fourier (cubeDifference f x) u‖ ^ 2 := by
      exact Finset.single_le_sum
        (f := fun u : ZMod N => ‖fourier (cubeDifference f x) u‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ r)
    _ = (N : Real) * ∑ s : ZMod N, ‖cubeDifference f x s‖ ^ 2 :=
      identity_2_3_holds N (cubeDifference f x)
    _ ≤ (N : Real) * ∑ s : ZMod N,
        ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (prop177_sum_cube_norm_sq_le_moment f x) (by positivity)

private lemma prop177_box_card_le {N k m : Nat} [NeZero N]
    (P : Box N k) (haxes : ∀ i, (P.axis i).length = m) :
    P.carrier.card ≤ m ^ k := by
  classical
  have hcarrier : P.carrier = Fintype.piFinset (fun i => (P.axis i).carrier) := by
    ext x
    simp [Box.carrier]
  rw [hcarrier, Fintype.card_piFinset]
  calc
    (∏ i : Fin k, (P.axis i).carrier.card) ≤ ∏ _i : Fin k, m := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le _
      · intro i _
        calc
          (P.axis i).carrier.card ≤ Fintype.card (Fin (P.axis i).length) := by
            unfold ModAP.carrier
            exact Finset.card_image_le
          _ = m := by simp [haxes i]
    _ = m ^ k := by simp

private lemma prop177_energy_implies_moment {N k m : Nat} [NeZero N]
    (f : ZMod N → Complex) (P : Box N k) (sigma : Point N k → ZMod N)
    (alpha : Real) (hm : 0 < m)
    (haxes : ∀ i, (P.axis i).length = m)
    (henergy : alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) :
    alpha * N ≤ ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := by
  let T : Real := ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1))
  have hPcard := prop177_box_card_le P haxes
  have hupper : (∑ x ∈ P.carrier,
      ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) ≤
      (m : Real) ^ k * ((N : Real) * T) := by
    calc
      _ ≤ ∑ _x ∈ P.carrier, (N : Real) * T := by
        exact Finset.sum_le_sum fun x _ => prop177_fourier_sq_le_moment f x (sigma x)
      _ = (P.carrier.card : Real) * ((N : Real) * T) := by simp [mul_comm]
      _ ≤ (m : Real) ^ k * ((N : Real) * T) := by
        gcongr
        exact_mod_cast hPcard
  have hchain := henergy.trans hupper
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  dsimp only [T] at hchain ⊢
  have hfac : 0 < (N : Real) * (m : Real) ^ k := mul_pos hN (pow_pos hmR _)
  have hscaled : ((N : Real) * (m : Real) ^ k) * (alpha * N) ≤
      ((N : Real) * (m : Real) ^ k) *
        (∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1))) := by
    nlinarith [hchain]
  exact le_of_mul_le_mul_left hscaled hfac

private lemma prop177_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma prop177_boolWeight_cons {n : Nat}
    (b : Bool) (e : Fin n → Bool) :
    boolWeight (Fin.cons b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  simp_rw [prop177_countWhere_eq_sum_ite]
  rw [Fin.sum_univ_succ]
  cases b <;> simp
  all_goals
    convert (@Finset.sum_boole (Fin n) Nat inferInstance
      (fun i : Fin n => e i = true)
      (fun i => Classical.propDecidable (e i = true))
      (Finset.univ : Finset (Fin n))).symm using 1
    all_goals simp only [Nat.cast_id]
  all_goals congr

private lemma prop177_parityConj_cons_false {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons false e) z = parityConj e z := by
  unfold parityConj
  rw [prop177_boolWeight_cons]
  simp

private lemma prop177_parityConj_cons_true {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons true e) z = star (parityConj e z) := by
  unfold parityConj
  rw [prop177_boolWeight_cons]
  have heven : Even (1 + boolWeight e) ↔ ¬Even (boolWeight e) := by
    rw [add_comm, Nat.even_add_one]
  by_cases h : Even (boolWeight e) <;> simp [heven, h]

private lemma prop177_parity_product_succ (n : Nat) (z : Complex) :
    (∏ e : Fin (n + 1) → Bool, parityConj e z) =
      (∏ e : Fin n → Bool, parityConj e z) *
        star (∏ e : Fin n → Bool, parityConj e z) := by
  let T : (Fin (n + 1) → Bool) → Complex := fun e => parityConj e z
  calc
    (∏ e : Fin (n + 1) → Bool, parityConj e z) =
        ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
      exact (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).prod_comp T |>.symm
    _ = (∏ e : Fin n → Bool, T (Fin.cons false e)) *
        ∏ e : Fin n → Bool, T (Fin.cons true e) := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
    _ = (∏ e : Fin n → Bool, parityConj e z) *
        star (∏ e : Fin n → Bool, parityConj e z) := by
      rw [star_prod]
      congr 1
      · apply Finset.prod_congr rfl
        intro e _
        exact prop177_parityConj_cons_false e z
      · apply Finset.prod_congr rfl
        intro e _
        exact prop177_parityConj_cons_true e z

private lemma prop177_parity_product_closed (n : Nat) (z : Complex) :
    (∏ e : Fin (n + 1) → Bool, parityConj e z) =
      ((‖z‖ ^ ((2 : Nat) ^ (n + 1)) : Real) : Complex) := by
  induction n with
  | zero =>
      rw [prop177_parity_product_succ]
      simp [parityConj, boolWeight, countWhere, Complex.mul_conj']
  | succ n ih =>
      rw [prop177_parity_product_succ, ih]
      rw [← starRingEnd_apply, Complex.conj_ofReal]
      push_cast
      rw [pow_succ]
      ring

private lemma prop177_singleton_carrier {N : Nat} (t : ZMod N) :
    (modInterval N t 1).carrier = {t} := by
  classical
  ext x
  simp [modInterval, ModAP.carrier]

private lemma prop177_singleton_cube_sum {N n : Nat} [NeZero N]
    (f : ZMod N → Complex) (t : ZMod N) :
    (∑ x : Point N (n + 1), ∑ s : ZMod N,
      cubeDifference (restrictToCell {t} f) x s) =
      ((‖f t‖ ^ ((2 : Nat) ^ (n + 1)) : Real) : Complex) := by
  classical
  let h := restrictToCell {t} f
  rw [← constant_cubeForm_eq_sum_cubeDifference h]
  unfold cubeForm
  rw [Finset.sum_eq_single (0 : Point N (n + 1))]
  · rw [Finset.sum_eq_single t]
    · have harg (e : Fin (n + 1) → Bool) :
          cubeArgument t (0 : Point N (n + 1)) e = t := by
        simp [cubeArgument]
      simp_rw [harg]
      simp only [h, restrictToCell, Finset.mem_singleton, if_true]
      exact prop177_parity_product_closed n (f t)
    · intro s _ hst
      let e0 := prop177ZeroVertex (n + 1)
      have harg : cubeArgument s (0 : Point N (n + 1)) e0 = s := by
        simp [cubeArgument, e0, prop177ZeroVertex]
      apply Finset.prod_eq_zero (Finset.mem_univ e0)
      rw [harg]
      simp [h, restrictToCell, hst, parityConj]
    · simp
  · intro x _ hx0
    have hnot : ¬ ∀ i, x i = 0 := by
      intro hz
      apply hx0
      funext i
      exact hz i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    let e : Fin (n + 1) → Bool := fun j => decide (j = i)
    have hsum : (∑ j, if e j then x j else 0) = x i := by
      simp [e]
    rw [Finset.sum_eq_zero]
    intro s _
    by_cases hst : s = t
    · subst s
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      have harg : cubeArgument t x e = t - x i := by
        simp [cubeArgument, hsum]
      rw [harg]
      have hne : t - x i ≠ t := by
        intro heq
        apply hi
        exact sub_eq_self.mp heq
      simp [h, restrictToCell, hne, parityConj]
    · let e0 := prop177ZeroVertex (n + 1)
      apply Finset.prod_eq_zero (Finset.mem_univ e0)
      have harg : cubeArgument s x e0 = s := by
        simp [cubeArgument, e0, prop177ZeroVertex]
      rw [harg]
      simp [h, restrictToCell, hst, parityConj]
  · simp

private def prop177SingletonCells (N : Nat) : Fin N → ModAP N :=
  fun i => modInterval N (i : ZMod N) 1

private lemma prop177_singleton_partition (N : Nat) [NeZero N] :
    IsPartition (fun i : Fin N => (prop177SingletonCells N i).carrier) Finset.univ := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_univ, true_iff]
    let i : Fin N := (prop177FinZModEquiv N).symm x
    refine ⟨i, ?_⟩
    rw [prop177SingletonCells, prop177_singleton_carrier]
    rw [Finset.mem_singleton]
    exact (prop177FinZModEquiv N).apply_symm_apply x |>.symm
  · intro i j hij
    change Disjoint (modInterval N (i : ZMod N) 1).carrier
      (modInterval N (j : ZMod N) 1).carrier
    rw [prop177_singleton_carrier, prop177_singleton_carrier]
    apply Finset.disjoint_singleton.mpr
    intro h
    apply bne_iff_ne.mp hij
    exact (prop177FinZModEquiv N).injective h

private lemma prop177_singleton_proper (N : Nat) [NeZero N] (i : Fin N) :
    (prop177SingletonCells N i).IsProper := by
  unfold ModAP.IsProper
  change (modInterval N (i : ZMod N) 1).carrier.card = 1
  rw [prop177_singleton_carrier]
  simp

private lemma prop177_singleton_uniform_sum {N k : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    (∑ i : Fin N, (∑ x : Point N (k + 1), ∑ s : ZMod N,
      cubeDifference
        (restrictToCell (prop177SingletonCells N i).carrier f) x s).re) =
      ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1)) := by
  calc
    _ = ∑ i : Fin N, ‖f ((prop177FinZModEquiv N) i)‖ ^ ((2 : Nat) ^ (k + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prop177SingletonCells, prop177_singleton_carrier,
        prop177_singleton_cube_sum]
      simp only [prop177FinZModEquiv, Equiv.coe_fn_mk]
      rw [Complex.ofReal_re]
    _ = _ := (prop177FinZModEquiv N).sum_comp
      (fun t => ‖f t‖ ^ ((2 : Nat) ^ (k + 1)))

@[simp] private lemma prop177_exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

private lemma prop177_small_coefficient_lt_one (k : Nat) (hk : 0 < k) :
    (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) *
        (2 : Real) ^ (k + 2) < 1 := by
  have heq : (2 * (k + 1) ^ 3 : Int) =
      (2 * (k + 1) ^ 3 : Nat) := by norm_num
  rw [heq, zpow_neg, zpow_natCast]
  rw [inv_mul_lt_one₀ (by positivity :
    0 < (2 : Real) ^ (2 * (k + 1) ^ 3))]
  apply pow_lt_pow_right₀ (by norm_num : (1 : Real) < 2)
  have hp : k + 1 ≤ (k + 1) ^ 3 := Nat.le_pow (by norm_num)
  omega

private theorem prop177_small_branch {N k m : Nat} [NeZero N]
    (f : ZMod N → Complex) (P : Box N k)
    (sigma : Point N k → ZMod N) (alpha : Real)
    (halpha : 0 < alpha) (hk : 0 < k) (hm : Odd m)
    (haxes : ∀ i, (P.axis i).length = m)
    (henergy : alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2)
    (hsmall : m ≤ 3 * k) :
    ∃ phi : ZMod N → ZMod N, ∃ M l : Nat,
      ∃ Q : Fin M → ModAP N,
        PolynomialOn (k + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧
          ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (m : Real) / (3 * k) ≤ l ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1) := by
  let phi : ZMod N → ZMod N := fun _ => 0
  let Q : Fin N → ModAP N := prop177SingletonCells N
  refine ⟨phi, N, 1, Q, ?_, prop177_singleton_partition N, ?_, ?_, ?_⟩
  · unfold PolynomialOn
    refine ⟨fun _ => 0, ?_⟩
    intro x _
    simp [phi]
  · intro i
    refine ⟨prop177_singleton_proper N i, Or.inl ?_⟩
    rfl
  · norm_num only [Nat.cast_one]
    apply (div_le_one (by positivity : (0 : Real) < 3 * k)).mpr
    exact_mod_cast hsmall
  · have hmpos : 0 < m := hm.pos
    have hmoment := prop177_energy_implies_moment f P sigma alpha hmpos haxes henergy
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hcoeff := prop177_small_coefficient_lt_one k hk
    have hstrict :
        (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha *
            (2 : Real) ^ (k + 2) * N < alpha * N := by
      calc
        _ = ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) *
              (2 : Real) ^ (k + 2)) * (alpha * N) := by ring
        _ < 1 * (alpha * N) :=
          mul_lt_mul_of_pos_right hcoeff (mul_pos halpha hN)
        _ = _ := by ring
    intro huniform
    have htwist : phaseTwist f phi = f := by
      funext s
      simp [phaseTwist, phi]
    unfold UniformOnPartition at huniform
    rw [htwist, prop177_singleton_uniform_sum] at huniform
    norm_num only [Nat.cast_one, one_add_one_eq_two, Nat.cast_ofNat] at huniform
    exact (not_le_of_gt (hstrict.trans_le hmoment)) huniform

/-! ### Mixed cube forms and affine phase removal -/

@[simp] private lemma prop177_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop177_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

private lemma prop177_fourier_sq {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    ((‖fourier g r‖ ^ 2 : Real) : Complex) =
      ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ s : ZMod N, exponential (-(s * r)) * g s‖ ^ 2 : Real) : Complex) =
        (∑ s : ZMod N, exponential (-(s * r)) * g s) *
          star (∑ t : ZMod N, exponential (-(t * r)) * g t) := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ s : ZMod N, ∑ t : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g t) * exponential (t * r)) := by
      simp only [star_sum, star_mul, prop177_star_exponential, neg_neg]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ s : ZMod N, ∑ y : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g (s - y)) * exponential ((s - y) * r)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← (Equiv.subLeft s).sum_comp]
      rfl
    _ = ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro s _
      have hphase :
          exponential (-(s * r)) * exponential ((s - y) * r) =
            exponential (-(y * r)) := by
        rw [← prop177_exponential_add]
        congr 1
        ring
      rw [← hphase]
      unfold difference
      ring

private lemma prop177_cubeDifference_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    cubeDifference f x s =
      ∏ e : Fin d → Bool, parityConj e (f (cubeArgument s x e)) := by
  induction d generalizing s with
  | zero =>
      simp [cubeDifference, iteratedDifference, parityConj, boolWeight,
        cubeArgument, countWhere]
  | succ n ih =>
      let r : ZMod N := x 0
      let a : Point N n := Fin.tail x
      have hx : x = Fin.cons r a := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hx, cubeDifference_cons]
      simp only [difference, ih]
      let T : (Fin (n + 1) → Bool) → Complex := fun e =>
        parityConj e (f (cubeArgument s (Fin.cons r a) e))
      calc
        (∏ e : Fin n → Bool, parityConj e (f (cubeArgument s a e))) *
            star (∏ e : Fin n → Bool,
              parityConj e (f (cubeArgument (s - r) a e))) =
            (∏ e : Fin n → Bool, T (Fin.cons false e)) *
              ∏ e : Fin n → Bool, T (Fin.cons true e) := by
          rw [star_prod]
          congr 1
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop177_parityConj_cons_false, prop177_cubeArgument_cons]
            simp only [Bool.false_eq_true, if_false, sub_zero]
            rfl
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop177_parityConj_cons_true, prop177_cubeArgument_cons]
            simp only [if_true]
            rfl
        _ = ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
        _ = ∏ e : Fin (n + 1) → Bool, T e := by
          exact (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).prod_comp T

private def prop177PhasedFamily {N d : Nat} [NeZero N]
    (H : (Fin d → Bool) → ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N) :
    (Fin d → Bool) → ZMod N → Complex :=
  fun e s => H e s * exponential (-(phi e s))

private lemma prop177_parity_phased {N d : Nat} [NeZero N]
    (H : (Fin d → Bool) → ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (e : Fin d → Bool) (z : ZMod N) :
    parityConj e (prop177PhasedFamily H phi e z) =
      parityConj e (H e z) * exponential
        (-(if Even (boolWeight e) then phi e z else -phi e z)) := by
  by_cases h : Even (boolWeight e)
  · simp [prop177PhasedFamily, parityConj, h]
  · simp [prop177PhasedFamily, parityConj, h, star_mul]
    ring

private lemma prop177_exponential_sum {N : Nat} [NeZero N]
    {I : Type*} (S : Finset I) (a : I → ZMod N) :
    exponential (∑ i ∈ S, a i) = ∏ i ∈ S, exponential (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih => simp [hx, ih]

private lemma prop177_phasedCubeProduct {N d : Nat} [NeZero N]
    (H : (Fin d → Bool) → ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (x : Point N d) (s : ZMod N) :
    (∏ e : Fin d → Bool,
      parityConj e
        (prop177PhasedFamily H phi e (cubeArgument s x e))) =
      (∏ e : Fin d → Bool,
        parityConj e (H e (cubeArgument s x e))) *
          exponential (-(signedCubeSum phi s x)) := by
  calc
    _ = ∏ e : Fin d → Bool,
        (parityConj e (H e (cubeArgument s x e)) *
          exponential (-(if Even (boolWeight e) then
            phi e (cubeArgument s x e)
          else -phi e (cubeArgument s x e)))) := by
      apply Finset.prod_congr rfl
      intro e _
      exact prop177_parity_phased H phi e (cubeArgument s x e)
    _ = (∏ e : Fin d → Bool,
          parityConj e (H e (cubeArgument s x e))) *
        ∏ e : Fin d → Bool,
          exponential (-(if Even (boolWeight e) then
            phi e (cubeArgument s x e)
          else -phi e (cubeArgument s x e))) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      congr 1
      rw [← prop177_exponential_sum Finset.univ]
      congr 1
      unfold signedCubeSum
      rw [Finset.sum_neg_distrib]

private lemma prop177_cubeForm_phased {N d : Nat} [NeZero N]
    (H : (Fin d → Bool) → ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (tau : Point N d → ZMod N)
    (hphase : ∀ s x, tau x = signedCubeSum phi s x) :
    cubeForm (prop177PhasedFamily H phi) =
      ∑ x : Point N d, ∑ s : ZMod N,
        (∏ e : Fin d → Bool,
          parityConj e (H e (cubeArgument s x e))) *
            exponential (-(tau x)) := by
  unfold cubeForm
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  rw [prop177_phasedCubeProduct, hphase s x]

private lemma prop177_difference_mixedProduct {N k : Nat}
    (H : (Fin k → Bool) → ZMod N → Complex)
    (a : Point N k) (y s : ZMod N) :
    difference
      (fun t => ∏ e : Fin k → Bool,
        parityConj e (H e (cubeArgument t a e))) y s =
      ∏ E : Fin (k + 1) → Bool,
        parityConj E
          (H (Fin.tail E)
            (cubeArgument s (Fin.cons y a : Point N (k + 1)) E)) := by
  unfold difference
  rw [star_prod]
  let T : (Fin (k + 1) → Bool) → Complex := fun E =>
    parityConj E
      (H (Fin.tail E)
        (cubeArgument s (Fin.cons y a : Point N (k + 1)) E))
  calc
    (∏ e : Fin k → Bool, parityConj e (H e (cubeArgument s a e))) *
        ∏ e : Fin k → Bool,
          star (parityConj e (H e (cubeArgument (s - y) a e))) =
      (∏ e : Fin k → Bool, T (Fin.cons false e)) *
        ∏ e : Fin k → Bool, T (Fin.cons true e) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro e _
        simp only [T, Fin.tail_cons]
        rw [prop177_parityConj_cons_false, prop177_cubeArgument_cons]
        simp only [Bool.false_eq_true, if_false, sub_zero]
        rfl
      · apply Finset.prod_congr rfl
        intro e _
        simp only [T, Fin.tail_cons]
        rw [prop177_parityConj_cons_true, prop177_cubeArgument_cons]
        simp only [if_true]
        rfl
    _ = ∏ p : Bool × (Fin k → Bool), T (Fin.cons p.1 p.2) := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
    _ = ∏ E : Fin (k + 1) → Bool, T E := by
      exact (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).prod_comp T

private lemma prop177_mixedEnergy_expansion {N k : Nat} [NeZero N]
    (H : (Fin k → Bool) → ZMod N → Complex)
    (tau : Point N k → ZMod N) :
    ((∑ a : Point N k,
        ‖∑ s : ZMod N, exponential (-(s * tau a)) *
          ∏ e : Fin k → Bool,
            parityConj e (H e (cubeArgument s a e))‖ ^ 2 : Real) : Complex) =
      ∑ z : Point N (k + 1), ∑ s : ZMod N,
        (∏ E : Fin (k + 1) → Bool,
          parityConj E
            (H (Fin.tail E) (cubeArgument s z E))) *
          exponential (-(z 0 * tau (Fin.tail z))) := by
  calc
    _ = ∑ a : Point N k,
        ((‖∑ s : ZMod N, exponential (-(s * tau a)) *
          ∏ e : Fin k → Bool,
            parityConj e (H e (cubeArgument s a e))‖ ^ 2 : Real) : Complex) := by
      rw [Complex.ofReal_sum]
    _ = ∑ a : Point N k, ∑ y : ZMod N, ∑ s : ZMod N,
        difference
          (fun t => ∏ e : Fin k → Bool,
            parityConj e (H e (cubeArgument t a e))) y s *
          exponential (-(y * tau a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact prop177_fourier_sq
        (fun t => ∏ e : Fin k → Bool,
          parityConj e (H e (cubeArgument t a e))) (tau a)
    _ = ∑ y : ZMod N, ∑ a : Point N k, ∑ s : ZMod N,
        (∏ E : Fin (k + 1) → Bool,
          parityConj E
            (H (Fin.tail E)
              (cubeArgument s (Fin.cons y a : Point N (k + 1)) E))) *
          exponential (-((Fin.cons y a : Point N (k + 1)) 0 *
            tau (Fin.tail (Fin.cons y a : Point N (k + 1))))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro s _
      rw [prop177_difference_mixedProduct]
      simp
    _ = _ := by
      exact (sum_point_succ (N := N) (n := k) (M := Complex)
        (fun z => ∑ s : ZMod N,
          (∏ E : Fin (k + 1) → Bool,
            parityConj E (H (Fin.tail E) (cubeArgument s z E))) *
              exponential (-(z 0 * tau (Fin.tail z))))).symm

private def prop177Monomial {N k : Nat} (e : Fin k → Bool)
    (x : Point N k) : ZMod N := ∏ i, if e i then x i else 1

private lemma prop177Monomial_cons {N k : Nat} (b : Bool)
    (e : Fin k → Bool) (z : Point N (k + 1)) :
    prop177Monomial (Fin.cons b e) z =
      (if b then z 0 else 1) * prop177Monomial e (Fin.tail z) := by
  simp [prop177Monomial, Fin.prod_univ_succ, Fin.tail]

private lemma prop177_multilinear_cons {N k : Nat}
    (sigma : Point N k → ZMod N) (hsigma : IsMultilinear sigma) :
    IsMultilinear (fun z : Point N (k + 1) =>
      z 0 * sigma (Fin.tail z)) := by
  classical
  obtain ⟨c, hc⟩ := hsigma
  let c' : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    if e 0 then c (Fin.tail e) else 0
  refine ⟨c', fun z => ?_⟩
  let T : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    c' e * prop177Monomial e z
  have htrue (e : Fin k → Bool) :
      T (Fin.cons true e) =
        z 0 * (c e * prop177Monomial e (Fin.tail z)) := by
    simp [T, c', prop177Monomial_cons]
    ring
  have hfalse (e : Fin k → Bool) : T (Fin.cons false e) = 0 := by
    simp [T, c']
  change z 0 * sigma (Fin.tail z) = ∑ e, T e
  calc
    z 0 * sigma (Fin.tail z) =
        z 0 * ∑ e : Fin k → Bool,
          c e * prop177Monomial e (Fin.tail z) := by
      rw [hc]
      rfl
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [htrue]
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) +
        ∑ e : Fin k → Bool, T (Fin.cons false e) := by simp [hfalse]
    _ = ∑ p : Bool × (Fin k → Bool), T (Fin.cons p.1 p.2) := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
    _ = ∑ e : Fin (k + 1) → Bool, T e := by
      exact (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp T

private def prop177TailOffset {N k : Nat} (r : Point N k)
    (E : Fin (k + 1) → Bool) : ZMod N :=
  ∑ i, if (Fin.tail E) i then r i else 0

private def prop177AffinePhase {N k : Nat} (d : ZMod N) (r : Point N k)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (E : Fin (k + 1) → Bool) (u : ZMod N) : ZMod N :=
  Phi E (d * u - prop177TailOffset r E)

private def prop177AffineTau {N k : Nat} (d : ZMod N) (r : Point N k)
    (sigma : Point N k → ZMod N) (a : Point N k) : ZMod N :=
  d * sigma (fun i => d * a i + r i)

private lemma prop177_affine_vertex_argument {N k : Nat}
    (d : ZMod N) (r : Point N k) (t : ZMod N)
    (z : Point N (k + 1)) (E : Fin (k + 1) → Bool) :
    d * cubeArgument t z E - prop177TailOffset r E =
      cubeArgument (d * t)
        (Fin.cons (d * z 0) (fun i => d * (Fin.tail z) i + r i) :
          Point N (k + 1)) E := by
  unfold cubeArgument prop177TailOffset
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
  change
    d * (t - ((if E 0 then z 0 else 0) +
        (∑ i : Fin k, if E i.succ then z i.succ else 0))) -
        (∑ i : Fin k, if E i.succ then r i else 0) =
      d * t - ((if E 0 then d * z 0 else 0) +
        (∑ i : Fin k, if E i.succ then d * z i.succ + r i else 0))
  rw [mul_sub, mul_add, Finset.mul_sum]
  cases E 0 <;> simp
  all_goals
    have hsum :
        (∑ i : Fin k, if E i.succ then d * z i.succ + r i else 0) =
          (∑ i : Fin k, if E i.succ then d * z i.succ else 0) +
            (∑ i : Fin k, if E i.succ then r i else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases E i.succ <;> simp
    rw [hsum]
    ring

private lemma prop177_affine_phase_identity {N k : Nat}
    (d : ZMod N) (r : Point N k) (sigma : Point N k → ZMod N)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (hPhi : ∀ s x,
      x 0 * sigma (Fin.tail x) = signedCubeSum Phi s x)
    (t : ZMod N) (z : Point N (k + 1)) :
    z 0 * prop177AffineTau d r sigma (Fin.tail z) =
      signedCubeSum (prop177AffinePhase d r Phi) t z := by
  have h := hPhi (d * t)
    (Fin.cons (d * z 0) (fun i => d * (Fin.tail z) i + r i) :
      Point N (k + 1))
  simp only [Fin.cons_zero, Fin.tail_cons] at h
  calc
    z 0 * prop177AffineTau d r sigma (Fin.tail z) =
        d * z 0 * sigma (fun i => d * (Fin.tail z) i + r i) := by
      unfold prop177AffineTau
      ring
    _ = signedCubeSum Phi (d * t)
        (Fin.cons (d * z 0) (fun i => d * (Fin.tail z) i + r i) :
          Point N (k + 1)) := h
    _ = signedCubeSum (prop177AffinePhase d r Phi) t z := by
      unfold signedCubeSum prop177AffinePhase
      apply Finset.sum_congr rfl
      intro E _
      rw [prop177_affine_vertex_argument]

/-! ### Parameterizing the input box -/

private abbrev prop177BoxParameter (k m : Nat) := Fin k → Fin m

private def prop177BoxPoint {N k m : Nat} (P : Box N k)
    (u : prop177BoxParameter k m) : Point N k :=
  fun i => (P.axis i).start + (u i : Nat) * P.commonDiff

private def prop177CenteredInt {k m : Nat} (h : Nat)
    (u : prop177BoxParameter k m) : Fin k → Int :=
  fun i => (u i : Nat) - (h : Int)

private def prop177BoxCenter {N k : Nat} (P : Box N k) (h : Nat) :
    Point N k :=
  fun i => (P.axis i).start + h * P.commonDiff

private lemma prop177_boxPoint_affine {N k m h : Nat} (P : Box N k)
    (u : prop177BoxParameter k m) (i : Fin k) :
    prop177BoxPoint P u i =
      P.commonDiff * (prop177CenteredInt h u i : ZMod N) +
        prop177BoxCenter P h i := by
  unfold prop177BoxPoint prop177CenteredInt prop177BoxCenter
  push_cast
  ring

private lemma prop177_boxPoint_injective {N k m : Nat} [NeZero N]
    [Fact N.Prime] (P : Box N k) (hd : P.commonDiff != 0)
    (hmN : m ≤ N) : Function.Injective (prop177BoxPoint (m := m) P) := by
  intro u v huv
  funext i
  apply Fin.ext
  have hi := congrFun huv i
  dsimp only [prop177BoxPoint] at hi
  have hmul : ((u i : Nat) : ZMod N) * P.commonDiff =
      ((v i : Nat) : ZMod N) * P.commonDiff := add_left_cancel hi
  have hcast : ((u i : Nat) : ZMod N) = ((v i : Nat) : ZMod N) :=
    (Equiv.mulRight₀ P.commonDiff (bne_iff_ne.mp hd)).injective hmul
  have huN : (u i : Nat) < N := lt_of_lt_of_le (u i).isLt hmN
  have hvN : (v i : Nat) < N := lt_of_lt_of_le (v i).isLt hmN
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast_of_lt huN,
    ZMod.val_natCast_of_lt hvN] using hval

private lemma prop177_box_carrier_eq_image {N k m : Nat} [NeZero N]
    (P : Box N k) (haxes : ∀ i, (P.axis i).length = m) :
    P.carrier = (Finset.univ : Finset (prop177BoxParameter k m)).image
      (prop177BoxPoint P) := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hx
    have hwitness (i : Fin k) : ∃ u : Fin m,
        x i = (P.axis i).start + (u : Nat) * P.commonDiff := by
      have hxi := hx i
      unfold ModAP.carrier at hxi
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxi
      obtain ⟨j, hj⟩ := hxi
      let u : Fin m := Fin.cast (haxes i) j
      refine ⟨u, ?_⟩
      rw [← hj, P.axis_step i]
      rfl
    choose u hu using hwitness
    refine ⟨u, ?_⟩
    funext i
    exact (hu i).symm
  · rintro ⟨u, rfl⟩ i
    unfold ModAP.carrier
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    let j : Fin (P.axis i).length := Fin.cast (haxes i).symm (u i)
    refine ⟨j, ?_⟩
    rw [P.axis_step i]
    rfl

private lemma prop177_energy_reindex_box {N k m : Nat} [NeZero N]
    [Fact N.Prime] (f : ZMod N → Complex) (P : Box N k)
    (sigma : Point N k → ZMod N)
    (haxes : ∀ i, (P.axis i).length = m)
    (hd : P.commonDiff != 0) (hmN : m ≤ N) :
    (∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) =
      ∑ u : prop177BoxParameter k m,
        ‖fourier (cubeDifference f (prop177BoxPoint P u))
          (sigma (prop177BoxPoint P u))‖ ^ 2 := by
  rw [prop177_box_carrier_eq_image P haxes,
    Finset.sum_image (prop177_boxPoint_injective P hd hmN).injOn]

private def prop177Offset {N k : Nat} (r : Point N k)
    (e : Fin k → Bool) : ZMod N :=
  ∑ i, if e i then r i else 0

private def prop177ShiftedVertex {N k : Nat} (f : ZMod N → Complex)
    (d : ZMod N) (r : Point N k) (e : Fin k → Bool)
    (u : ZMod N) : Complex :=
  f (d * u - prop177Offset r e)

private lemma prop177_affine_cubeArgument {N k : Nat}
    (d : ZMod N) (r a : Point N k) (t : ZMod N)
    (e : Fin k → Bool) :
    cubeArgument (d * t) (fun i => d * a i + r i) e =
      d * cubeArgument t a e - prop177Offset r e := by
  unfold cubeArgument prop177Offset
  change d * t -
      (∑ i : Fin k, if e i then d * a i + r i else 0) =
    d * (t - ∑ i : Fin k, if e i then a i else 0) -
      ∑ i : Fin k, if e i then r i else 0
  have hsum :
      (∑ i : Fin k, if e i then d * a i + r i else 0) =
        (∑ i : Fin k, if e i then d * a i else 0) +
          (∑ i : Fin k, if e i then r i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases e i <;> simp
  rw [hsum]
  rw [mul_sub, Finset.mul_sum]
  have hmul :
      (∑ i : Fin k, if e i then d * a i else 0) =
        ∑ i : Fin k, d * (if e i then a i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    cases e i <;> simp
  rw [hmul]
  ring

private lemma prop177_fourier_boxPoint {N k m h : Nat} [NeZero N]
    [Fact N.Prime] (f : ZMod N → Complex) (P : Box N k)
    (sigma : Point N k → ZMod N) (hd : P.commonDiff != 0)
    (u : prop177BoxParameter k m) :
    fourier (cubeDifference f (prop177BoxPoint P u))
        (sigma (prop177BoxPoint P u)) =
      ∑ t : ZMod N,
        exponential (-(t * prop177AffineTau P.commonDiff
          (prop177BoxCenter P h) sigma
          (fun i => (prop177CenteredInt h u i : ZMod N)))) *
        ∏ e : Fin k → Bool,
          parityConj e
            (prop177ShiftedVertex f P.commonDiff (prop177BoxCenter P h) e
              (t - ∑ i, if e i then
                (prop177CenteredInt h u i : ZMod N) else 0)) := by
  let d := P.commonDiff
  let r := prop177BoxCenter P h
  let a : Point N k := fun i => (prop177CenteredInt h u i : ZMod N)
  have hx : prop177BoxPoint P u = fun i => d * a i + r i := by
    funext i
    exact prop177_boxPoint_affine P u i
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  rw [← (Equiv.mulLeft₀ d (bne_iff_ne.mp hd)).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [prop177_cubeDifference_product]
  change exponential (-((d * t) * sigma (prop177BoxPoint P u))) *
      (∏ e : Fin k → Bool,
        parityConj e
          (f (cubeArgument (d * t) (prop177BoxPoint P u) e))) = _
  have htau : t * prop177AffineTau d r sigma a =
      (d * t) * sigma (prop177BoxPoint P u) := by
    rw [hx]
    unfold prop177AffineTau
    ring
  rw [htau]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  unfold prop177ShiftedVertex
  rw [hx, prop177_affine_cubeArgument]
  rfl
  · simp

private def prop177CenteredPoint {N k m : Nat} (h : Nat)
    (u : prop177BoxParameter k m) : Point N k :=
  fun i => (prop177CenteredInt h u i : ZMod N)

private lemma prop177_centeredPoint_injective {N k m h : Nat} [NeZero N]
    (hmN : m ≤ N) : Function.Injective
      (prop177CenteredPoint (N := N) (k := k) (m := m) h) := by
  intro u v huv
  funext i
  apply Fin.ext
  have hi := congrFun huv i
  have hcast : ((u i : Nat) : ZMod N) = ((v i : Nat) : ZMod N) := by
    dsimp only [prop177CenteredPoint, prop177CenteredInt] at hi
    push_cast at hi
    have := congrArg (fun z : ZMod N => z + (h : ZMod N)) hi
    simpa only [sub_add_cancel] using this
  have huN : (u i : Nat) < N := lt_of_lt_of_le (u i).isLt hmN
  have hvN : (v i : Nat) < N := lt_of_lt_of_le (v i).isLt hmN
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast_of_lt huN,
    ZMod.val_natCast_of_lt hvN] using hval

private lemma prop177_sum_centered_le_univ {N k m h : Nat} [NeZero N]
    (hmN : m ≤ N) (G : Point N k → Real)
    (hG : ∀ a, 0 ≤ G a) :
    (∑ u : prop177BoxParameter k m, G (prop177CenteredPoint h u)) ≤
      ∑ a : Point N k, G a := by
  classical
  rw [← Finset.sum_image
    (prop177_centeredPoint_injective (N := N) (k := k) (h := h) hmN).injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro a _ _
  exact hG a

private def prop177LocalInner {N M k : Nat} [NeZero N] [NeZero M]
    (_hM : 0 < M) (f : ZMod N → Complex) (d : ZMod N)
    (r : Point N k) (sigma : Point N k → ZMod N)
    (g : (Fin k → Bool) → ZMod M) (c : ZMod M)
    (a : Point N k) : Complex :=
  ∑ t : ZMod N,
    exponential (-(t * prop177AffineTau d r sigma a)) *
      ∏ e : Fin k → Bool,
        parityConj e
          (restrictToCell
            (prop177ResidueCell N M (g e + c)).carrier
            (prop177ShiftedVertex f d r e)
            (cubeArgument t a e))

private lemma prop177_fourier_eq_localized_sum
    {N M k m h : Nat} [NeZero N] [Fact N.Prime] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (P : Box N k)
    (sigma : Point N k → ZMod N) (hd : P.commonDiff != 0)
    (F : Finset ((Fin k → Bool) → ZMod M))
    (hFzero : ∀ g, g ∈ F → g (prop177ZeroVertex k) = 0)
    (hFmem : ∀ (a0 : Real) (a : Fin k → Real),
      (∀ i, -((k + 1 : Nat) : Real) < a i ∧
        a i < (k + 1 : Nat)) →
      (fun e => floorAffinePattern (M := M) a0 a e -
        floorAffinePattern (M := M) a0 a (prop177ZeroVertex k)) ∈ F)
    (u : prop177BoxParameter k m)
    (ha : ∀ i,
      -((k + 1 : Nat) : Real) <
          -((prop177CenteredInt h u i : Int) : Real) /
            prop177CellWidth N M ∧
      -((prop177CenteredInt h u i : Int) : Real) /
          prop177CellWidth N M < (k + 1 : Nat)) :
    fourier (cubeDifference f (prop177BoxPoint P u))
        (sigma (prop177BoxPoint P u)) =
      ∑ g ∈ F, ∑ c : ZMod M,
        prop177LocalInner hM f P.commonDiff (prop177BoxCenter P h)
          sigma g c (prop177CenteredPoint h u) := by
  rw [prop177_fourier_boxPoint f P sigma hd u]
  let aInt := prop177CenteredInt h u
  let H : (Fin k → Bool) → ZMod N → Complex :=
    fun e => prop177ShiftedVertex f P.commonDiff (prop177BoxCenter P h) e
  have hdecomp (t : ZMod N) :=
    prop177_support_decomposition hM F hFzero H t aInt
      (prop177_normalized_raw_mem hM F hFmem t aInt ha)
  unfold prop177LocalInner
  change (∑ t : ZMod N,
      exponential (-(t * prop177AffineTau P.commonDiff
        (prop177BoxCenter P h) sigma (prop177CenteredPoint h u))) *
        ∏ e : Fin k → Bool,
          parityConj e
            (H e (t - ∑ i, if e i then (aInt i : ZMod N) else 0))) = _
  calc
    _ = ∑ t : ZMod N,
        exponential (-(t * prop177AffineTau P.commonDiff
          (prop177BoxCenter P h) sigma (prop177CenteredPoint h u))) *
          ∑ g ∈ F, ∑ c : ZMod M,
            ∏ e : Fin k → Bool,
              parityConj e
                (restrictToCell
                  (prop177ResidueCell N M (g e + c)).carrier (H e)
                  (t - ∑ i, if e i then (aInt i : ZMod N) else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hdecomp t]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
      rfl

private lemma prop177_norm_sum_sq_le_card {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → Complex) :
    ‖∑ i ∈ S, z i‖ ^ 2 ≤
      (S.card : Real) * ∑ i ∈ S, ‖z i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using sq_sum_le_card_mul_sum_sq
        (s := S) (f := fun i => ‖z i‖)

private lemma prop177_select_double_sum
    {U G C : Type*} [Fintype U] [Fintype C]
    [DecidableEq G] [DecidableEq C] (F : Finset G) (hF : F.Nonempty)
    (V : G → C → U → Complex) (A : Real)
    (hA : A ≤ ∑ u : U, ‖∑ g ∈ F, ∑ c : C, V g c u‖ ^ 2) :
    ∃ g ∈ F, A ≤
      (F.card : Real) ^ 2 * Fintype.card C *
        ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2 := by
  let E : G → Real := fun g => ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2
  have houter (u : U) :
      ‖∑ g ∈ F, ∑ c : C, V g c u‖ ^ 2 ≤
        (F.card : Real) * ∑ g ∈ F, ‖∑ c : C, V g c u‖ ^ 2 :=
    prop177_norm_sum_sq_le_card F (fun g => ∑ c : C, V g c u)
  have hinner (g : G) (u : U) :
      ‖∑ c : C, V g c u‖ ^ 2 ≤
        (Fintype.card C : Real) * ∑ c : C, ‖V g c u‖ ^ 2 := by
    simpa only [Finset.card_univ] using
      prop177_norm_sum_sq_le_card (Finset.univ : Finset C)
        (fun c => V g c u)
  have htotal : A ≤
      (F.card : Real) * Fintype.card C * ∑ g ∈ F, E g := by
    calc
      A ≤ ∑ u : U, ‖∑ g ∈ F, ∑ c : C, V g c u‖ ^ 2 := hA
      _ ≤ ∑ u : U,
          (F.card : Real) * ∑ g ∈ F, ‖∑ c : C, V g c u‖ ^ 2 :=
        Finset.sum_le_sum fun u _ => houter u
      _ ≤ ∑ u : U,
          (F.card : Real) * ∑ g ∈ F,
            (Fintype.card C : Real) * ∑ c : C, ‖V g c u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        gcongr with g hg
        exact hinner g u
      _ = (F.card : Real) * Fintype.card C * ∑ g ∈ F, E g := by
        unfold E
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        ring_nf
  obtain ⟨g, hgF, hgmax⟩ := Finset.exists_max_image F E hF
  refine ⟨g, hgF, ?_⟩
  have hsum : (∑ x ∈ F, E x) ≤ (F.card : Real) * E g := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id] using
      Finset.sum_le_card_nsmul F E (E g) hgmax
  calc
    A ≤ (F.card : Real) * Fintype.card C * ∑ x ∈ F, E x := htotal
    _ ≤ (F.card : Real) * Fintype.card C * ((F.card : Real) * E g) := by
      gcongr
    _ = (F.card : Real) ^ 2 * Fintype.card C *
        ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2 := by
      unfold E
      ring

private def prop177ExtendedLocalFamily {N M k : Nat} [NeZero M]
    (_hM : 0 < M) (f : ZMod N → Complex) (d : ZMod N)
    (r : Point N k) (g : (Fin k → Bool) → ZMod M) (c : ZMod M) :
    (Fin (k + 1) → Bool) → ZMod N → Complex :=
  fun E => restrictToCell
    (prop177ResidueCell N M (g (Fin.tail E) + c)).carrier
    (prop177ShiftedVertex f d r (Fin.tail E))

private lemma prop177_local_energy_eq_cubeForm_norm
    {N M k : Nat} [NeZero N] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (d : ZMod N)
    (r : Point N k) (sigma : Point N k → ZMod N)
    (g : (Fin k → Bool) → ZMod M) (c : ZMod M)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (hPhi : ∀ s x,
      x 0 * sigma (Fin.tail x) = signedCubeSum Phi s x) :
    ‖cubeForm (prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi))‖ =
      ∑ a : Point N k, ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2 := by
  let H : (Fin k → Bool) → ZMod N → Complex := fun e =>
    restrictToCell (prop177ResidueCell N M (g e + c)).carrier
      (prop177ShiftedVertex f d r e)
  let E : Real := ∑ a : Point N k, ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2
  have hphase (s : ZMod N) (z : Point N (k + 1)) :
      z 0 * prop177AffineTau d r sigma (Fin.tail z) =
        signedCubeSum (prop177AffinePhase d r Phi) s z :=
    prop177_affine_phase_identity d r sigma Phi hPhi s z
  have hform : cubeForm (prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi)) = (E : Complex) := by
    calc
      _ = ∑ z : Point N (k + 1), ∑ s : ZMod N,
          (∏ E : Fin (k + 1) → Bool,
            parityConj E
              (H (Fin.tail E) (cubeArgument s z E))) *
            exponential (-(z 0 * prop177AffineTau d r sigma (Fin.tail z))) := by
        simpa only [H, prop177ExtendedLocalFamily] using
          prop177_cubeForm_phased
            (prop177ExtendedLocalFamily hM f d r g c)
            (prop177AffinePhase d r Phi)
            (fun z => z 0 * prop177AffineTau d r sigma (Fin.tail z)) hphase
      _ = (E : Complex) := by
        rw [← prop177_mixedEnergy_expansion H
          (prop177AffineTau d r sigma)]
        congr 2
  rw [hform, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] private lemma prop177_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

private lemma prop177_local_phased_discValued
    {N M k : Nat} [NeZero N] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (hf : DiscValued f)
    (d : ZMod N) (r : Point N k)
    (g : (Fin k → Bool) → ZMod M) (c : ZMod M)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (E : Fin (k + 1) → Bool) :
    DiscValued (prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi) E) := by
  intro s
  unfold prop177PhasedFamily prop177ExtendedLocalFamily
  rw [norm_mul, prop177_norm_exponential, mul_one]
  unfold restrictToCell prop177ShiftedVertex
  split_ifs
  · exact hf _
  · simp

private lemma prop177_select_local_vertex
    {N M k : Nat} [NeZero N] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (hf : DiscValued f)
    (d : ZMod N) (r : Point N k) (sigma : Point N k → ZMod N)
    (g : (Fin k → Bool) → ZMod M)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (hPhi : ∀ s x,
      x 0 * sigma (Fin.tail x) = signedCubeSum Phi s x) :
    ∃ E : Fin (k + 1) → Bool,
      (∑ a : Point N k, ∑ c : ZMod M,
        ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2) ≤
      ∑ c : ZMod M,
        ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
          prop177PhasedFamily
            (prop177ExtendedLocalFamily hM f d r g c)
            (prop177AffinePhase d r Phi) E)‖ := by
  let n : Nat := 2 ^ (k + 1)
  let w : Real := (n : Real)⁻¹
  let G : ZMod M → (Fin (k + 1) → Bool) → Real := fun c E =>
    ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
      prop177PhasedFamily
        (prop177ExtendedLocalFamily hM f d r g c)
        (prop177AffinePhase d r Phi) E)‖
  let T : (Fin (k + 1) → Bool) → Real := fun E => ∑ c : ZMod M, G c E
  have hn : n ≠ 0 := by positivity
  have hnpos : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hw : 0 < w := inv_pos.mpr hnpos
  have hweight : ∑ _E : Fin (k + 1) → Bool, w = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, n, w,
      Nat.cast_pow, Nat.cast_ofNat]
    apply mul_inv_cancel₀
    positivity
  have hG (c : ZMod M) (E : Fin (k + 1) → Bool) : 0 ≤ G c E :=
    norm_nonneg _
  have hper (c : ZMod M) :
      (∑ a : Point N k,
        ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2) ≤
        ∑ E : Fin (k + 1) → Bool, w * G c E := by
    let A := prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi)
    have hdisc : ∀ E, DiscValued (A E) := fun E =>
      prop177_local_phased_discValued hM f hf d r g c Phi E
    have hgcs := lemma_3_8_holds N (k + 1) A hdisc
    have hgeom :
        ‖cubeForm A‖ ≤ ∏ E : Fin (k + 1) → Bool, (G c E) ^ w := by
      calc
        ‖cubeForm A‖ ≤ ∏ E : Fin (k + 1) → Bool,
            ‖cubeForm (d := k + 1)
              (fun (_ : Fin (k + 1) → Bool) => A E)‖ ^
                ((1 : Real) / (2 : Real) ^ (k + 1)) := hgcs
        _ = ∏ E : Fin (k + 1) → Bool, (G c E) ^ w := by
          apply Finset.prod_congr rfl
          intro E _
          congr 2
          simp only [w, n, one_div, Nat.cast_pow, Nat.cast_ofNat]
    have hamgm : (∏ E : Fin (k + 1) → Bool, (G c E) ^ w) ≤
        ∑ E : Fin (k + 1) → Bool, w * G c E := by
      exact Real.geom_mean_le_arith_mean_weighted Finset.univ
        (fun _ => w) (G c) (fun _ _ => hw.le) hweight
        (fun E _ => hG c E)
    rw [← prop177_local_energy_eq_cubeForm_norm
      hM f d r sigma g c Phi hPhi]
    exact hgeom.trans hamgm
  have htotal :
      (∑ a : Point N k, ∑ c : ZMod M,
        ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2) ≤
        ∑ E : Fin (k + 1) → Bool, w * T E := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ c : ZMod M,
          ∑ E : Fin (k + 1) → Bool, w * G c E :=
        Finset.sum_le_sum fun c _ => hper c
      _ = _ := by
        rw [Finset.sum_comm]
        unfold T
        apply Finset.sum_congr rfl
        intro E _
        rw [Finset.mul_sum]
  have hU : (Finset.univ : Finset (Fin (k + 1) → Bool)).Nonempty := by
    exact Finset.univ_nonempty
  obtain ⟨E, _, hEmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (k + 1) → Bool)) T hU
  refine ⟨E, htotal.trans ?_⟩
  calc
    (∑ E' : Fin (k + 1) → Bool, w * T E') ≤
        ∑ _E' : Fin (k + 1) → Bool, w * T E := by
      apply Finset.sum_le_sum
      intro E' _
      exact mul_le_mul_of_nonneg_left (hEmax E' (Finset.mem_univ E')) hw.le
    _ = T E := by
      rw [← Finset.sum_mul, hweight, one_mul]
    _ = ∑ c : ZMod M,
        ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
          prop177PhasedFamily
            (prop177ExtendedLocalFamily hM f d r g c)
            (prop177AffinePhase d r Phi) E)‖ := rfl

/-! ### Transporting the selected cell and phase -/

private def prop177MapCell {N : Nat} (d offset : ZMod N)
    (Q : ModAP N) : ModAP N where
  start := d * Q.start - offset
  step := d * Q.step
  length := Q.length

private lemma prop177_mapCell_mem_iff {N : Nat} [NeZero N]
    [Fact N.Prime] (d offset : ZMod N) (hd : d ≠ 0)
    (Q : ModAP N) (u : ZMod N) :
    d * u - offset ∈ (prop177MapCell d offset Q).carrier ↔
      u ∈ Q.carrier := by
  classical
  unfold prop177MapCell ModAP.carrier
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have := congrArg (fun z : ZMod N => z + offset) hi
    apply mul_left_cancel₀ hd
    calc
      d * (Q.start + (i : Nat) * Q.step) =
          (d * Q.start - offset + (i : Nat) * (d * Q.step)) + offset := by
        ring
      _ = d * u := by
        simpa only [sub_add_cancel, Nat.cast_comm] using this
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    ring

private def prop177AffineEquiv {N : Nat} [NeZero N] [Fact N.Prime]
    (d offset : ZMod N) (hd : d ≠ 0) : ZMod N ≃ ZMod N :=
  (Equiv.mulLeft₀ d hd).trans (Equiv.subRight offset)

private lemma prop177_affineEquiv_apply {N : Nat} [NeZero N] [Fact N.Prime]
    (d offset : ZMod N) (hd : d ≠ 0) (u : ZMod N) :
    prop177AffineEquiv d offset hd u = d * u - offset := rfl

private lemma prop177_cubeArgument_affine {N q : Nat}
    (d offset : ZMod N) (s : ZMod N) (x : Point N q)
    (e : Fin q → Bool) :
    cubeArgument (d * s - offset) (fun i => d * x i) e =
      d * cubeArgument s x e - offset := by
  unfold cubeArgument
  change d * s - offset -
      (∑ i : Fin q, if e i then d * x i else 0) =
    d * (s - ∑ i : Fin q, if e i then x i else 0) - offset
  have hsum :
      (∑ i : Fin q, if e i then d * x i else 0) =
        ∑ i : Fin q, d * (if e i then x i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    cases e i <;> simp
  rw [hsum]
  rw [mul_sub, Finset.mul_sum]
  ring

private lemma prop177_constantCubeForm_affine {N q : Nat} [NeZero N]
    [Fact N.Prime] (d offset : ZMod N) (hd : d ≠ 0)
    (h : ZMod N → Complex) :
    cubeForm (d := q) (fun _ : Fin q → Bool =>
      fun u => h (d * u - offset)) =
      cubeForm (d := q) (fun _ : Fin q → Bool => h) := by
  let eS := prop177AffineEquiv d offset hd
  let eX : Point N q ≃ Point N q :=
    Equiv.piCongrRight (fun _ : Fin q => Equiv.mulLeft₀ d hd)
  symm
  unfold cubeForm
  rw [← eX.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [← eS.sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.prod_congr rfl
  intro e _
  rw [show eS s = d * s - offset by rfl]
  rw [show eX x = (fun i => d * x i) by rfl]
  rw [prop177_cubeArgument_affine]

private lemma prop177_constantCubeForm_norm_eq_real_sum
    {N k : Nat} [NeZero N] (h : ZMod N → Complex) :
    ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool => h)‖ =
      ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference h x s).re := by
  let R : Real := ∑ x : Point N k,
    ‖∑ s : ZMod N, cubeDifference h x s‖ ^ 2
  have hcomplex :
      (∑ x : Point N (k + 1), ∑ s : ZMod N,
        cubeDifference h x s) = (R : Complex) := by
    exact sum_cube_succ_eq_sum_norm_sq h
  have hnorm :
      ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool => h)‖ = R := by
    rw [constant_cubeForm_eq_sum_cubeDifference, hcomplex,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hnorm]
  calc
    R = (∑ x : Point N (k + 1), ∑ s : ZMod N,
        cubeDifference h x s).re := by rw [hcomplex, Complex.ofReal_re]
    _ = ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference h x s).re := by simp

private lemma prop177_selected_constant_form_transport
    {N M k : Nat} [NeZero N] [Fact N.Prime] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (d : ZMod N)
    (hd : d ≠ 0) (r : Point N k)
    (g : (Fin k → Bool) → ZMod M) (c : ZMod M)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (E : Fin (k + 1) → Bool) :
    ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
      prop177PhasedFamily
        (prop177ExtendedLocalFamily hM f d r g c)
        (prop177AffinePhase d r Phi) E)‖ =
      ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference
          (restrictToCell
            (prop177MapCell d (prop177TailOffset r E)
              (prop177ResidueCell N M (g (Fin.tail E) + c))).carrier
            (phaseTwist f (Phi E))) x s).re := by
  let offset := prop177TailOffset r E
  let Q := prop177ResidueCell N M (g (Fin.tail E) + c)
  let hOrig := restrictToCell (prop177MapCell d offset Q).carrier
    (phaseTwist f (Phi E))
  have hoff : prop177Offset r (Fin.tail E) = offset := rfl
  have hfun : prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi) E =
      fun u => hOrig (d * u - offset) := by
    funext u
    unfold prop177PhasedFamily prop177ExtendedLocalFamily
    unfold prop177ShiftedVertex prop177AffinePhase hOrig
    rw [hoff]
    have hmem := prop177_mapCell_mem_iff d offset hd Q u
    unfold restrictToCell phaseTwist
    by_cases hu : u ∈ Q.carrier
    · rw [if_pos hu, if_pos (hmem.mpr hu)]
    · rw [if_neg hu, if_neg (fun h => hu (hmem.mp h))]
      simp
  rw [hfun, prop177_constantCubeForm_affine d offset hd hOrig]
  exact prop177_constantCubeForm_norm_eq_real_sum hOrig

private def prop177OutputCell (N M : Nat) (d offset : ZMod N)
    (i : Fin M) : ModAP N :=
  prop177MapCell d offset (prop177BalancedCell N M i)

private lemma prop177_mapCell_carrier {N : Nat} [NeZero N]
    [Fact N.Prime] (d offset : ZMod N) (hd : d ≠ 0) (Q : ModAP N) :
    (prop177MapCell d offset Q).carrier =
      Q.carrier.image (fun u => d * u - offset) := by
  classical
  ext x
  let e := prop177AffineEquiv d offset hd
  let u := e.symm x
  have heu : d * u - offset = x := by
    exact e.apply_symm_apply x
  simp only [Finset.mem_image]
  constructor
  · intro hx
    refine ⟨u, ?_, heu⟩
    apply (prop177_mapCell_mem_iff d offset hd Q u).mp
    rwa [heu]
  · rintro ⟨u', hu', rfl⟩
    exact (prop177_mapCell_mem_iff d offset hd Q u').mpr hu'

private lemma prop177_output_partition {N M : Nat} [NeZero N]
    [Fact N.Prime] (hM : 0 < M) (d offset : ZMod N) (hd : d ≠ 0) :
    IsPartition
      (fun i : Fin M => (prop177OutputCell N M d offset i).carrier)
      Finset.univ := by
  classical
  let e := prop177AffineEquiv d offset hd
  constructor
  · intro x
    simp only [Finset.mem_univ, true_iff]
    let u := e.symm x
    let i := prop177CellIndex hM u
    refine ⟨i, ?_⟩
    unfold prop177OutputCell
    have hu : u ∈ (prop177BalancedCell N M i).carrier :=
      (prop177_balancedCell_mem_iff_index hM i u).mpr rfl
    have hmap := prop177_mapCell_mem_iff d offset hd
      (prop177BalancedCell N M i) u
    have heu : d * u - offset = x := e.apply_symm_apply x
    rw [heu] at hmap
    exact hmap.mpr hu
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    let u := e.symm x
    have heu : d * u - offset = x := e.apply_symm_apply x
    have hui : u ∈ (prop177BalancedCell N M i).carrier := by
      apply (prop177_mapCell_mem_iff d offset hd
        (prop177BalancedCell N M i) u).mp
      simpa only [prop177OutputCell, heu] using hxi
    have huj : u ∈ (prop177BalancedCell N M j).carrier := by
      apply (prop177_mapCell_mem_iff d offset hd
        (prop177BalancedCell N M j) u).mp
      simpa only [prop177OutputCell, heu] using hxj
    have hi := (prop177_balancedCell_mem_iff_index hM i u).mp hui
    have hj := (prop177_balancedCell_mem_iff_index hM j u).mp huj
    exact bne_iff_ne.mp hij (hi.symm.trans hj)

private lemma prop177_output_proper {N M : Nat} [NeZero N]
    [Fact N.Prime] (hM : 0 < M) (d offset : ZMod N) (hd : d ≠ 0)
    (i : Fin M) : (prop177OutputCell N M d offset i).IsProper := by
  classical
  unfold ModAP.IsProper prop177OutputCell
  rw [prop177_mapCell_carrier d offset hd]
  rw [Finset.card_image_iff.mpr]
  · exact prop177_balancedCell_isProper hM i
  · intro x _ y _ hxy
    apply (prop177AffineEquiv d offset hd).injective
    exact hxy

private lemma prop177_output_length {N M : Nat}
    (d offset : ZMod N) (i : Fin M) :
    (prop177OutputCell N M d offset i).length =
      (prop177BalancedCell N M i).length := rfl

private lemma prop177_transport_sum_reindex
    {N M k : Nat} [NeZero N] [Fact N.Prime] [NeZero M]
    (hM : 0 < M) (f : ZMod N → Complex) (d : ZMod N)
    (hd : d ≠ 0) (r : Point N k)
    (g : (Fin k → Bool) → ZMod M)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (E : Fin (k + 1) → Bool) :
    (∑ c : ZMod M,
      ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
        prop177PhasedFamily
          (prop177ExtendedLocalFamily hM f d r g c)
          (prop177AffinePhase d r Phi) E)‖) =
      ∑ i : Fin M, ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference
          (restrictToCell
            (prop177OutputCell N M d (prop177TailOffset r E) i).carrier
            (phaseTwist f (Phi E))) x s).re := by
  let A : ZMod M → Real := fun j =>
    ∑ x : Point N (k + 1), ∑ s : ZMod N,
      (cubeDifference
        (restrictToCell
          (prop177MapCell d (prop177TailOffset r E)
            (prop177ResidueCell N M j)).carrier
          (phaseTwist f (Phi E))) x s).re
  calc
    _ = ∑ c : ZMod M, A (g (Fin.tail E) + c) := by
      apply Finset.sum_congr rfl
      intro c _
      exact prop177_selected_constant_form_transport
        hM f d hd r g c Phi E
    _ = ∑ j : ZMod M, A j :=
      Equiv.sum_comp (Equiv.addLeft (g (Fin.tail E))) A
    _ = ∑ i : Fin M, A (prop177FinZModEquiv M i) :=
      (prop177FinZModEquiv M).sum_comp A |>.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      unfold A prop177OutputCell prop177ResidueCell
      rw [(prop177FinZModEquiv M).symm_apply_apply]

private lemma prop177_factorial_unit {N q : Nat} [NeZero N]
    [Fact N.Prime] (hqN : q < N) :
    IsUnit ((Nat.factorial q : Nat) : ZMod N) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply IsUnit.mul
      · rw [isUnit_iff_ne_zero]
        intro hz
        rw [ZMod.natCast_eq_zero_iff] at hz
        have hpos : 0 < q + 1 := by omega
        exact (Nat.not_lt_of_ge (Nat.le_of_dvd hpos hz)) hqN
      · exact ih (Nat.lt_trans (Nat.lt_succ_self q) hqN)

private def prop177Scale (h k : Nat) : Nat :=
  Nat.ceil ((h : Real) / k)

private lemma prop177_scale_bounds {N h k : Nat}
    (hk : 0 < k) (hlarge : 3 * k < 2 * h + 1)
    (hSq : (((2 * h + 1 : Nat) : Real) ^ 2) ≤ (N : Real)) :
    0 < prop177Scale h k ∧
      prop177Scale h k + 1 ≤ 2 * h + 1 ∧
      prop177Scale h k * prop177Scale h k ≤ N ∧
      (((2 * h + 1 : Nat) : Real) / (3 * k) : Real) ≤
        prop177Scale h k := by
  let q := prop177Scale h k
  have hh : 0 < h := by omega
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have hhR : (0 : Real) < h := by exact_mod_cast hh
  have hratio0 : (0 : Real) < (h : Real) / k := div_pos hhR hkR
  have hqpos : 0 < q := by
    exact Nat.ceil_pos.mpr hratio0
  have hqLower : (h : Real) / k ≤ (q : Real) := by
    exact Nat.le_ceil ((h : Real) / k)
  have hkOne : (1 : Real) ≤ k := by exact_mod_cast hk
  have hratioUpper : (h : Real) / k ≤ (h : Real) := by
    rw [div_le_iff₀ hkR]
    nlinarith
  have hqle : q ≤ h := by
    exact Nat.ceil_le.mpr hratioUpper
  have hqSucc : q + 1 ≤ 2 * h + 1 := by omega
  have hqSqR : ((q : Real) ^ 2) ≤ (N : Real) := by
    calc
      ((q : Real) ^ 2) ≤ (((2 * h + 1 : Nat) : Real) ^ 2) := by
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (show q ≤ 2 * h + 1 by omega)
      _ ≤ (N : Real) := hSq
  have hqSq : q * q ≤ N := by
    have : q ^ 2 ≤ N := by exact_mod_cast hqSqR
    simpa [pow_two] using this
  have hmThree : (2 * h + 1 : Nat) ≤ 3 * h := by omega
  have hlowerRatio :
      (((2 * h + 1 : Nat) : Real) / (3 * k) : Real) ≤
        (h : Real) / k := by
    rw [div_le_div_iff₀ (by positivity : (0 : Real) < 3 * k) hkR]
    exact_mod_cast (show (2 * h + 1) * k ≤ h * (3 * k) by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        Nat.mul_le_mul_right k hmThree)
  exact ⟨hqpos, hqSucc, hqSq, hlowerRatio.trans hqLower⟩

private lemma prop177_quotient_width_bounds {N q : Nat}
    (hq : 0 < q) (hqSq : q * q ≤ N) :
    let M := N / q
    0 < M ∧ q ≤ M ∧
      (q : Real) ≤ prop177CellWidth N M ∧
      prop177CellWidth N M < q + 1 := by
  let M := N / q
  have hqN : q ≤ N := by
    have hqq : q ≤ q * q := by nlinarith
    exact hqq.trans hqSq
  have hM : 0 < M := Nat.div_pos hqN hq
  have hqM : q ≤ M := by
    exact (Nat.le_div_iff_mul_le hq).mpr hqSq
  have hMReal : (0 : Real) < M := by exact_mod_cast hM
  have hqWidth : (q : Real) ≤ prop177CellWidth N M := by
    unfold prop177CellWidth
    rw [le_div_iff₀ hMReal]
    exact_mod_cast (show q * M ≤ N by
      simpa [M, mul_comm] using Nat.div_mul_le_self N q)
  have hNlt : N < M * q + q := by
    simpa only [M] using Nat.lt_div_mul_add (a := N) hq
  have hNlt' : N < (q + 1) * M := by
    calc
      N < M * q + q := hNlt
      _ ≤ M * q + M := Nat.add_le_add_left hqM (M * q)
      _ = (q + 1) * M := by ring
  have hWidthQ : prop177CellWidth N M < q + 1 := by
    unfold prop177CellWidth
    rw [div_lt_iff₀ hMReal]
    exact_mod_cast hNlt'
  exact ⟨hM, hqM, hqWidth, hWidthQ⟩

private lemma prop177_centered_int_bounds {k h : Nat}
    (u : prop177BoxParameter k (2 * h + 1)) (i : Fin k) :
    -((h : Nat) : Real) ≤
        ((prop177CenteredInt h u i : Int) : Real) ∧
      ((prop177CenteredInt h u i : Int) : Real) ≤ (h : Real) := by
  have hui : (u i : Nat) ≤ 2 * h := by omega
  have hInt : -(h : Int) ≤ (u i : Nat) - (h : Int) ∧
      (u i : Nat) - (h : Int) ≤ (h : Int) := by
    constructor <;> omega
  dsimp only [prop177CenteredInt]
  exact_mod_cast hInt

private lemma prop177_centered_coefficient_bound {N M k h q : Nat}
    (hk : 0 < k) (hM : 0 < M) (hqpos : 0 < q)
    (hqLower : (h : Real) / k ≤ (q : Real))
    (hqW : (q : Real) ≤ prop177CellWidth N M)
    (u : prop177BoxParameter k (2 * h + 1)) (i : Fin k) :
    -((k + 1 : Nat) : Real) <
          -((prop177CenteredInt h u i : Int) : Real) /
            prop177CellWidth N M ∧
      -((prop177CenteredInt h u i : Int) : Real) /
          prop177CellWidth N M < (k + 1 : Nat) := by
  have hN : 0 < N := by
    by_contra hn
    have : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    unfold prop177CellWidth at hqW
    simp only [Nat.cast_zero, zero_div] at hqW
    have hq0 : q = 0 := by
      have : (q : Real) ≤ 0 := hqW
      exact_mod_cast ((Nat.cast_nonneg q).antisymm this).symm
    omega
  have hw : 0 < prop177CellWidth N M := prop177_width_pos hN hM
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have hhW : (h : Real) ≤ (k : Real) * prop177CellWidth N M := by
    have hhq : (h : Real) ≤ (k : Real) * q := by
      simpa [mul_comm] using (div_le_iff₀ hkR).mp hqLower
    nlinarith
  obtain ⟨hzL, hzU⟩ := prop177_centered_int_bounds u i
  norm_num only [Nat.cast_add, Nat.cast_one]
  constructor
  · rw [lt_div_iff₀ hw]
    nlinarith
  · rw [div_lt_iff₀ hw]
    nlinarith

private lemma prop177_pattern_coefficient_lt_quarter (k : Nat) (hk : 0 < k) :
    (((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2) *
        (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) < 1 / 4 := by
  let a := k * (k + 1) ^ 2
  let b := 2 * (k + 1) ^ 3
  have hexp : 2 + 2 * a < b := by
    dsimp only [a, b]
    nlinarith [sq_pos_of_pos (show (0 : Real) < k by exact_mod_cast hk)]
  have hpowNat : 4 * (2 ^ a) ^ 2 < 2 ^ b := by
    calc
      4 * (2 ^ a) ^ 2 = 2 ^ (2 + 2 * a) := by ring
      _ < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hexp
  have hpowReal :
      (4 : Real) * (((2 ^ a : Nat) : Real) ^ 2) < (2 : Real) ^ b := by
    exact_mod_cast hpowNat
  have hden : (0 : Real) < (2 : Real) ^ b := by positivity
  have hdiv :
      (((2 ^ a : Nat) : Real) ^ 2) / ((2 : Real) ^ b) < 1 / 4 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : Real) < 4)]
    nlinarith
  change (((2 ^ a : Nat) : Real) ^ 2) *
      (2 : Real) ^ (-(b : Int)) < 1 / 4
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact hdiv

private lemma prop177_quantitative_strict
    {N k m q M : Nat} (alpha S : Real)
    (halpha : 0 < alpha) (hk : 0 < k) (hq : 0 < q) (hM : 0 < M)
    (hqMleN : q * M ≤ N) (hqm : q + 1 ≤ m)
    (hraw : alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      (((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2) * M * S) :
    (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha *
        ((q + 1 : Nat) : Real) ^ (k + 2) * M < S := by
  let L : Real := ((2 ^ (k * (k + 1) ^ 2) : Nat) : Real)
  let c : Real := (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int))
  have hcoeff : L ^ 2 * c < 1 / 4 := by
    exact prop177_pattern_coefficient_lt_quarter k hk
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hMR : (0 : Real) < M := by exact_mod_cast hM
  have hqhalf : (((q + 1 : Nat) : Real)) ≤ 2 * (q : Real) := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have hqSquare :
      (1 / 4 : Real) * (((q + 1 : Nat) : Real) ^ 2) ≤
        (q : Real) ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hqhalf ⊢
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ q + 1)
      hqhalf 2
    nlinarith
  have hNM : (q : Real) * M ≤ (N : Real) := by
    exact_mod_cast hqMleN
  have hmR : (((q + 1 : Nat) : Real)) ≤ (m : Real) := by
    exact_mod_cast hqm
  have hscale :
      (1 / 4 : Real) * (((q + 1 : Nat) : Real) ^ (k + 2)) *
          (M : Real) ^ 2 ≤
        (N : Real) ^ 2 * (m : Real) ^ k := by
    calc
      _ = ((1 / 4 : Real) * (((q + 1 : Nat) : Real) ^ 2)) *
          (M : Real) ^ 2 * (((q + 1 : Nat) : Real) ^ k) := by
            rw [pow_add]
            ring
      _ ≤ ((q : Real) ^ 2) * (M : Real) ^ 2 * (m : Real) ^ k := by
        gcongr
      _ = ((q : Real) * M) ^ 2 * (m : Real) ^ k := by ring
      _ ≤ (N : Real) ^ 2 * (m : Real) ^ k := by
        gcongr
  have hfactor :
      L ^ 2 * (M : Real) *
          (c * alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * M) <
        alpha * (N : Real) ^ 2 * (m : Real) ^ k := by
    calc
      _ = (L ^ 2 * c) *
          (alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * (M : Real) ^ 2) := by
            ring
      _ < (1 / 4 : Real) *
          (alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * (M : Real) ^ 2) := by
        gcongr
      _ ≤ alpha * ((N : Real) ^ 2 * (m : Real) ^ k) := by
        calc
          _ = alpha * ((1 / 4 : Real) *
              (((q + 1 : Nat) : Real) ^ (k + 2)) * (M : Real) ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hscale halpha.le
      _ = _ := by ring
  change c * alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * M < S
  by_contra hnot
  have hS : S ≤ c * alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * M :=
    le_of_not_gt hnot
  have hupper : L ^ 2 * (M : Real) * S ≤
      L ^ 2 * (M : Real) *
        (c * alpha * (((q + 1 : Nat) : Real) ^ (k + 2)) * M) := by
    gcongr
  exact (not_lt_of_ge (hraw.trans hupper)) hfactor

private lemma prop177_double_sum_re
    {I J : Type*} [Fintype I] [Fintype J] (z : I → J → Complex) :
    (∑ i : I, ∑ j : J, z i j).re =
      ∑ i : I, ∑ j : J, (z i j).re := by
  change Complex.reCLM (∑ i : I, ∑ j : J, z i j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  simp only [Complex.reCLM_apply]

private theorem prop177_large_branch
    {N k h : Nat} [NeZero N] [Fact N.Prime]
    (f : ZMod N → Complex) (P : Box N k)
    (sigma : Point N k → ZMod N) (alpha : Real)
    (halpha : 0 < alpha) (hk : 0 < k)
    (hlarge : 3 * k < 2 * h + 1)
    (haxes : ∀ i, (P.axis i).length = 2 * h + 1)
    (hd : P.commonDiff != 0)
    (hmsqrt : (((2 * h + 1 : Nat) : Real)) ≤ Real.sqrt N)
    (hf : DiscValued f) (hsigma : IsMultilinear sigma)
    (henergy :
      alpha * (N : Real) ^ 2 * (((2 * h + 1 : Nat) : Real) ^ k) ≤
        ∑ x ∈ P.carrier,
          ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) :
    ∃ phi : ZMod N → ZMod N, ∃ M l : Nat,
      ∃ Q : Fin M → ModAP N,
        PolynomialOn (k + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧
          ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (((2 * h + 1 : Nat) : Real) / (3 * k) : Real) ≤ l ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1) := by
  have hN0 : (0 : Real) ≤ (N : Real) := by positivity
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : Real) := Real.sq_sqrt hN0
  have hmSq : (((2 * h + 1 : Nat) : Real) ^ 2) ≤ (N : Real) := by
    nlinarith [Real.sqrt_nonneg (N : Real)]
  have hmNReal : (((2 * h + 1 : Nat) : Real)) ≤ (N : Real) := by
    have hmOne : (1 : Real) ≤ ((2 * h + 1 : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ 2 * h + 1 by omega)
    nlinarith
  have hmN : 2 * h + 1 ≤ N := by exact_mod_cast hmNReal
  have hkN : k + 1 < N := by omega
  have hkfac : IsUnit ((Nat.factorial (k + 1) : Nat) : ZMod N) :=
    prop177_factorial_unit hkN
  let q := prop177Scale h k
  obtain ⟨hqpos, hqSucc, hqSq, hlower⟩ :=
    prop177_scale_bounds (N := N) hk hlarge hmSq
  let M := N / q
  obtain ⟨hMpos, hqM, hqWidth, hWidthUpper⟩ :=
    prop177_quotient_width_bounds (N := N) (q := q) hqpos hqSq
  letI : NeZero M := ⟨hMpos.ne'⟩
  have hqLower : (h : Real) / k ≤ (q : Real) := by
    exact Nat.le_ceil ((h : Real) / k)
  obtain ⟨F, hFcard, hFzero, hFmem⟩ :=
    prop177_exists_normalized_mod_patterns k M hk
  have hFnonempty : F.Nonempty := by
    let a0 : Real := 0
    let a : Fin k → Real := fun _ => 0
    have ha : ∀ i, -((k + 1 : Nat) : Real) < a i ∧
        a i < (k + 1 : Nat) := by
      intro i
      dsimp only [a]
      norm_num only [Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith [show (0 : Real) < k by exact_mod_cast hk]
    exact ⟨_, hFmem a0 a ha⟩
  let A : Real := alpha * (N : Real) ^ 2 *
    (((2 * h + 1 : Nat) : Real) ^ k)
  have hlocalized : A ≤
      ∑ u : prop177BoxParameter k (2 * h + 1),
        ‖∑ g ∈ F, ∑ c : ZMod M,
          prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
            sigma g c (prop177CenteredPoint h u)‖ ^ 2 := by
    calc
      A ≤ ∑ x ∈ P.carrier,
          ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 := henergy
      _ = ∑ u : prop177BoxParameter k (2 * h + 1),
          ‖fourier (cubeDifference f (prop177BoxPoint P u))
            (sigma (prop177BoxPoint P u))‖ ^ 2 :=
        prop177_energy_reindex_box f P sigma haxes hd hmN
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [prop177_fourier_eq_localized_sum
          (h := h) hMpos f P sigma hd F hFzero hFmem u]
        intro i
        exact prop177_centered_coefficient_bound hk hMpos hqpos
          hqLower hqWidth u i
  obtain ⟨g, hgF, hgSelect⟩ := prop177_select_double_sum
    F hFnonempty
      (fun g c u =>
        prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
          sigma g c (prop177CenteredPoint h u)) A hlocalized
  simp only [ZMod.card] at hgSelect
  let T : Real := ∑ a : Point N k, ∑ c : ZMod M,
    ‖prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
      sigma g c a‖ ^ 2
  have hExtend :
      (∑ u : prop177BoxParameter k (2 * h + 1), ∑ c : ZMod M,
        ‖prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
          sigma g c (prop177CenteredPoint h u)‖ ^ 2) ≤ T := by
    dsimp only [T]
    exact prop177_sum_centered_le_univ (h := h) hmN
      (fun a => ∑ c : ZMod M,
        ‖prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
          sigma g c a‖ ^ 2)
      (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hSelected : A ≤ (F.card : Real) ^ 2 * (M : Real) * T := by
    calc
      A ≤ (F.card : Real) ^ 2 * (M : Real) *
          ∑ u : prop177BoxParameter k (2 * h + 1), ∑ c : ZMod M,
            ‖prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h)
              sigma g c (prop177CenteredPoint h u)‖ ^ 2 := hgSelect
      _ ≤ _ := by gcongr
  let L : Nat := 2 ^ (k * (k + 1) ^ 2)
  have hFcardR : (F.card : Real) ≤ (L : Real) := by exact_mod_cast hFcard
  have hTnonneg : 0 ≤ T := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSelectedL : A ≤ (L : Real) ^ 2 * (M : Real) * T := by
    calc
      A ≤ (F.card : Real) ^ 2 * (M : Real) * T := hSelected
      _ ≤ (L : Real) ^ 2 * (M : Real) * T := by gcongr
  let rho : Point N (k + 1) → ZMod N := fun z =>
    z 0 * sigma (Fin.tail z)
  have hrho : IsMultilinear rho := prop177_multilinear_cons sigma hsigma
  obtain ⟨Phi, hPhiPoly, hPhi⟩ :=
    lemma_17_1_holds N (k + 1) hkN hkfac rho hrho
  obtain ⟨E, hVertex⟩ := prop177_select_local_vertex hMpos f hf
    P.commonDiff (prop177BoxCenter P h) sigma g Phi hPhi
  have hTVertex : T ≤
      ∑ c : ZMod M,
        ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
          prop177PhasedFamily
            (prop177ExtendedLocalFamily hMpos f P.commonDiff
              (prop177BoxCenter P h) g c)
            (prop177AffinePhase P.commonDiff (prop177BoxCenter P h) Phi) E)‖ := by
    exact hVertex
  have hSelectedVertex : A ≤
      (L : Real) ^ 2 * (M : Real) *
        ∑ c : ZMod M,
          ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool =>
            prop177PhasedFamily
              (prop177ExtendedLocalFamily hMpos f P.commonDiff
                (prop177BoxCenter P h) g c)
              (prop177AffinePhase P.commonDiff (prop177BoxCenter P h) Phi) E)‖ := by
    exact hSelectedL.trans (mul_le_mul_of_nonneg_left hTVertex (by positivity))
  have hSelectedTransport : A ≤
      (L : Real) ^ 2 * (M : Real) *
        ∑ i : Fin M, ∑ x : Point N (k + 1), ∑ s : ZMod N,
          (cubeDifference
            (restrictToCell
              (prop177OutputCell N M P.commonDiff
                (prop177TailOffset (prop177BoxCenter P h) E) i).carrier
              (phaseTwist f (Phi E))) x s).re := by
    rw [← prop177_transport_sum_reindex hMpos f P.commonDiff
      (bne_iff_ne.mp hd) (prop177BoxCenter P h) g Phi E]
    exact hSelectedVertex
  let Q : Fin M → ModAP N := fun i =>
    prop177OutputCell N M P.commonDiff
      (prop177TailOffset (prop177BoxCenter P h) E) i
  refine ⟨Phi E, M, q, Q, hPhiPoly E, ?_, ?_, hlower, ?_⟩
  · exact prop177_output_partition hMpos P.commonDiff
      (prop177TailOffset (prop177BoxCenter P h) E) (bne_iff_ne.mp hd)
  · intro i
    refine ⟨prop177_output_proper hMpos P.commonDiff
      (prop177TailOffset (prop177BoxCenter P h) E) (bne_iff_ne.mp hd) i, ?_⟩
    rw [prop177_output_length]
    exact prop177_boundary_increment (NeZero.pos N) hMpos hqWidth hWidthUpper i
  · intro hUniform
    have hqMleN : q * M ≤ N := by
      simpa only [M, mul_comm] using Nat.div_mul_le_self N q
    have hStrict := prop177_quantitative_strict alpha
      (∑ i : Fin M, ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference
          (restrictToCell
            (prop177OutputCell N M P.commonDiff
              (prop177TailOffset (prop177BoxCenter P h) E) i).carrier
            (phaseTwist f (Phi E))) x s).re)
      halpha hk hqpos hMpos hqMleN hqSucc
      (by simpa only [A, L] using hSelectedTransport)
    unfold UniformOnPartition at hUniform
    apply (not_le_of_gt hStrict)
    simp_rw [prop177_double_sum_re] at hUniform
    simpa only [Q, q, M] using hUniform

/-- **Gowers, Proposition 17.7.** -/
theorem proposition_17_7_holds : proposition_17_7 := by
  unfold proposition_17_7
  intro N k m _ _ f P sigma alpha halpha hk hm _hwidth haxes hd
    hmsqrt hf hsigma henergy
  by_cases hsmall : m ≤ 3 * k
  · exact prop177_small_branch f P sigma alpha halpha hk hm haxes
      henergy hsmall
  · have hlarge : 3 * k < m := lt_of_not_ge hsmall
    obtain ⟨h, rfl⟩ := hm
    exact prop177_large_branch f P sigma alpha halpha hk hlarge haxes hd
      hmsqrt hf hsigma henergy




end LeanProofs.GowersSzemeredi
