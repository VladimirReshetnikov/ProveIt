import GowersSzemeredi.Proofs17Regions
import GowersSzemeredi.Proofs17PhaseRemoval
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Localized polynomial phase removal

This file develops Proposition 17.7, whose assembled form
`proposition_17_7_holds` is in `Proofs17LocalizedPhaseRemovalSide`.  The proof
includes the balanced modular interval partition and the sharper count of
floor-affine patterns modulo constant translations that are used in the
localized argument.

`prop177Monomial`, `prop177Monomial_cons`, `prop177_affineEquiv_apply`,
`prop177_balancedCell_partition`, `prop177_boundary_zero` and
`proposition_17_7_holds` are in `Proofs17LocalizedPhaseRemovalSide`, outside the
final route. -/

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
  let S := Finset.univ.filter fun i => y i < b i
  obtain ⟨delta, hzero, hbound⟩ := Finset.exists_between' ({0} : Finset Real)
    (S.image fun i => b i - y i) (by
      intro a ha c hc
      obtain rfl := Finset.mem_singleton.mp ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      exact sub_pos.mpr (Finset.mem_filter.mp hi).2)
  refine ⟨delta, hzero 0 (Finset.mem_singleton_self _), ?_⟩
  intro i hi
  have h := hbound (b i - y i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩)
  linarith

private lemma prop177_floor_sub_floor_eq_fract (a s : Real) :
    ⌊a + s⌋ - ⌊a⌋ = ⌊Int.fract a + s⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]

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
  have hb (i : Fin k) : -((k + 1 : Nat) : Real) < (if e i then a i else 0) ∧
      (if e i then a i else 0) < (k + 1 : Nat) := by
    have h0 : (0 : Real) < (k + 1 : Nat) := by positivity
    split_ifs
    · exact ha i
    · exact ⟨by linarith, h0⟩
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hlo := Finset.sum_lt_sum_of_nonempty hne fun i _ => (hb i).1
  have hhi := Finset.sum_lt_sum_of_nonempty hne fun i _ => (hb i).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  unfold prop177SubsetSum
  push_cast at hlo hhi ⊢
  constructor <;> linarith

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
  obtain ⟨delta, hdelta, hsmall⟩ := prop177_exists_small_positive
    (fun q : Prop177Threshold k (k * (k + 1)) => prop177SubsetSum a q.1.1 + Int.fract a0)
    (fun q => (q.2.1 : Real))
  refine ⟨Fin.lastCases delta (Fin.lastCases (Int.fract a0) a), fun i => ?_⟩
  have hcode : prop177ThresholdCode (prop177BoundedPatternOf hk a0 a ha) i = true ↔
      prop177SubsetSum a (prop177ThresholdEquiv k (k * (k + 1)) i).1.1 + Int.fract a0 <
        (prop177ThresholdEquiv k (k * (k + 1)) i).2.1 := by
    simp only [prop177ThresholdCode, decide_eq_true_eq, prop177BoundedPatternOf,
      prop177NormalizedFloorPattern, prop177_floor_sub_floor_eq_fract]
    rw [add_comm]
    exact Int.floor_lt
  have hdot : realDot (prop177ThresholdHyperplanes k (k * (k + 1)) i).normal
      (Fin.lastCases delta (Fin.lastCases (Int.fract a0) a)) =
        prop177SubsetSum a (prop177ThresholdEquiv k (k * (k + 1)) i).1.1 + Int.fract a0 +
          delta :=
    prop177_realDot_threshold k (k * (k + 1)) (prop177ThresholdEquiv k (k * (k + 1)) i)
      (Int.fract a0) delta a
  rw [Bool.eq_false_iff, ne_eq, hcode, hdot]
  exact ⟨⟨hsmall _, (lt_add_of_pos_right _ hdelta).trans⟩,
    ⟨fun h => (not_lt.mp h).trans_lt (lt_add_of_pos_right _ hdelta),
      fun h h' => lt_asymm (hsmall _ h') h⟩⟩

private lemma prop177_thresholdCode_injective {k R : Nat} (_hR : 0 < R)
    {g h : Prop177BoundedPattern k R}
    (hg0 : (g (prop177ZeroVertex k)).1 = 0)
    (hh0 : (h (prop177ZeroVertex k)).1 = 0)
    (hcode : prop177ThresholdCode g = prop177ThresholdCode h) : g = h := by
  -- equal codes rule out `h e < g e`: the threshold `g e` separates them
  have key : ∀ {g h : Prop177BoundedPattern k R},
      prop177ThresholdCode g = prop177ThresholdCode h →
        ∀ e, e ≠ prop177ZeroVertex k → ¬ (h e).1 < (g e).1 := by
    intro g h hcode e he hlt
    have hg := Finset.mem_Icc.mp (g e).2
    have hh := Finset.mem_Icc.mp (h e).2
    have hc := congrFun hcode ((prop177ThresholdEquiv k R).symm
      ⟨⟨e, he⟩, ⟨(g e).1, Finset.mem_Icc.mpr ⟨by omega, hg.2⟩⟩⟩)
    simp [prop177ThresholdCode, hlt] at hc
  funext e
  apply Subtype.ext
  by_cases he0 : e = prop177ZeroVertex k
  · subst e
    exact hg0.trans hh0.symm
  · exact le_antisymm (not_lt.mp (key hcode e he0)) (not_lt.mp (key hcode.symm e he0))

private lemma prop177_thresholdCount_eq (k R : Nat) :
    prop177ThresholdCount k R = (2 ^ k - 1) * (2 * R) := by
  simp only [prop177ThresholdCount, Prop177Threshold, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unique]
  congr 1
  rw [Fintype.card_coe, Int.card_Icc]
  omega

private lemma prop177_two_mul_k_succ_le_pow (k : Nat) :
    2 * k * (k + 1) ≤ 2 ^ (2 * k + 2) := by
  have hk : k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
  have hks : k + 1 ≤ 2 ^ (k + 1) := Nat.le_of_lt (k + 1).lt_two_pow_self
  calc
    2 * k * (k + 1) ≤ 2 * 2 ^ k * 2 ^ (k + 1) := by gcongr
    _ = 2 ^ (k + 1) * 2 ^ (k + 1) := by ring
    _ = 2 ^ ((k + 1) + (k + 1)) :=
      (pow_add 2 (k + 1) (k + 1)).symm
    _ = 2 ^ (2 * k + 2) := by ring

private lemma prop177_thresholdCount_le_pow (k : Nat) :
    prop177ThresholdCount k (k * (k + 1)) ≤ 2 ^ (3 * k + 2) := by
  rw [prop177_thresholdCount_eq]
  calc
    (2 ^ k - 1) * (2 * (k * (k + 1))) ≤
        2 ^ k * 2 ^ (2 * k + 2) := by
      apply Nat.mul_le_mul
      · exact Nat.sub_le _ _
      · simpa [mul_assoc] using prop177_two_mul_k_succ_le_pow k
    _ = 2 ^ (3 * k + 2) := by ring

private lemma prop177_region_sum_bound (k : Nat) (hk : 0 < k) :
    (∑ j ∈ Finset.range (k + 3),
        Nat.choose (prop177ThresholdCount k (k * (k + 1))) j) ≤
      2 ^ (k * (k + 1) ^ 2) := by
  let n := prop177ThresholdCount k (k * (k + 1))
  by_cases hk4 : 4 ≤ k
  · have hn2 : 2 ≤ n := by
      have h1 : 2 ≤ 2 ^ k := Nat.le_self_pow hk.ne' 2
      have h2 : 0 < k * (k + 1) := by positivity
      have h3 : 2 ≤ 2 * (k * (k + 1)) := by omega
      rw [show n = (2 ^ k - 1) * (2 * (k * (k + 1))) from prop177_thresholdCount_eq k _]
      exact h3.trans (Nat.le_mul_of_pos_left _ (by omega))
    calc (∑ j ∈ Finset.range (k + 3), Nat.choose n j)
        ≤ ∑ j ∈ Finset.range (k + 3), n ^ j :=
          Finset.sum_le_sum fun j _ => Nat.choose_le_pow _ _
      _ ≤ 2 * n ^ (k + 2) := sum_range_pow_le_two_mul_pow n (k + 2) hn2
      _ ≤ 2 * (2 ^ (3 * k + 2)) ^ (k + 2) := by
        gcongr
        exact prop177_thresholdCount_le_pow k
      _ = 2 ^ ((3 * k + 2) * (k + 2) + 1) := by rw [← pow_mul, ← pow_succ']
      _ ≤ 2 ^ (k * (k + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
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
  refine ⟨S.image fun g e => (g e).1, ?_, fun g hg => ?_, fun a0 a ha => ?_⟩
  · calc _ ≤ S.card := Finset.card_image_le
      _ = (S.image prop177ThresholdCode).card :=
        (Finset.card_image_of_injOn fun g hg h hh hcode =>
          prop177_thresholdCode_injective (Nat.mul_pos hk k.succ_pos)
            (Finset.mem_filter.mp hg).2.1 (Finset.mem_filter.mp hh).2.1 hcode).symm
      _ ≤ hyperplaneRegionCount (prop177ThresholdHyperplanes k R) := by
        unfold hyperplaneRegionCount countWhere
        refine Finset.card_le_card fun p hp => ?_
        obtain ⟨g, hgS, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨-, a0, a, ha, rfl⟩ := (Finset.mem_filter.mp hgS).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, prop177_thresholdCode_realized hk a0 a ha⟩
      _ ≤ ∑ j ∈ Finset.range (k + 3), Nat.choose (prop177ThresholdCount k R) j := by
        simpa only [Nat.add_assoc] using
          (lemma_17_4_holds (k + 2) _ (prop177ThresholdHyperplanes k R)).1
      _ ≤ 2 ^ (k * (k + 1) ^ 2) := prop177_region_sum_bound k hk
  · obtain ⟨g', hgS, rfl⟩ := Finset.mem_image.mp hg
    exact (Finset.mem_filter.mp hgS).2.1
  · exact Finset.mem_image.mpr ⟨prop177BoundedPatternOf hk a0 a ha, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, prop177_normalizedFloor_zero a0 a, a0, a, ha, rfl⟩, rfl⟩

private theorem prop177_exists_normalized_mod_patterns (k M : Nat)
    (hk : 0 < k) :
    ∃ F : Finset ((Fin k → Bool) → ZMod M),
      F.card ≤ 2 ^ (k * (k + 1) ^ 2) ∧
      (∀ g, g ∈ F → g (prop177ZeroVertex k) = 0) ∧
      ∀ (a0 : Real) (a : Fin k → Real),
        (∀ i, -((k + 1 : Nat) : Real) < a i ∧ a i < (k + 1 : Nat)) →
        (fun e => floorAffinePattern (M := M) a0 a e -
          floorAffinePattern (M := M) a0 a (prop177ZeroVertex k)) ∈ F := by
  obtain ⟨G, hGcard, hGzero, hGmem⟩ := prop177_exists_normalized_integer_patterns k hk
  refine ⟨G.image fun g e => (g e : ZMod M), Finset.card_image_le.trans hGcard,
    fun _ hmem => ?_, fun a0 a ha => Finset.mem_image.mpr ⟨_, hGmem a0 a ha, ?_⟩⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hmem
    simp [hGzero g hg]
  · funext e
    simp only [prop177NormalizedFloorPattern, floorAffinePattern, prop177SubsetSum,
      prop177ZeroVertex, Bool.false_eq_true, if_false, Finset.sum_const_zero, add_zero,
      Int.cast_sub]

/-! ### Balanced modular interval partitions -/

def prop177CellWidth (N M : Nat) : Real := (N : Real) / M

def prop177Boundary (N M i : Nat) : Nat :=
  Nat.ceil ((i : Real) * prop177CellWidth N M)

def prop177BalancedCell (N M : Nat) (i : Fin M) : ModAP N :=
  modInterval N (prop177Boundary N M i : ZMod N)
    (prop177Boundary N M (i + 1) - prop177Boundary N M i)

private lemma prop177_width_pos {N M : Nat} (hN : 0 < N) (hM : 0 < M) :
    0 < prop177CellWidth N M := by
  unfold prop177CellWidth
  positivity

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
  rw [prop177BalancedCell, prop177_modInterval_mem_iff_val hend, Nat.add_sub_of_le hmono]

def prop177CellIndex {N M : Nat} [NeZero N]
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
  rw [Fin.ext_iff]
  change Nat.floor ((x.val : Real) / prop177CellWidth N M) = (i : Nat) ↔
    Nat.ceil ((i : Real) * prop177CellWidth N M) ≤ x.val ∧
      x.val < Nat.ceil ((((i : Nat) + 1 : Nat) : Real) * prop177CellWidth N M)
  rw [Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hw.le), Nat.ceil_le, Nat.lt_ceil,
    le_div_iff₀ hw, div_lt_iff₀ hw]
  push_cast
  rfl

lemma prop177_balancedCell_mem_iff_index {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) (x : ZMod N) :
    x ∈ (prop177BalancedCell N M i).carrier ↔ prop177CellIndex hM x = i := by
  rw [prop177_balancedCell_mem_iff hM, prop177_cellIndex_spec]

private lemma prop177_balancedCell_isProper {N M : Nat} [NeZero N]
    (hM : 0 < M) (i : Fin M) : (prop177BalancedCell N M i).IsProper := by
  have hL : prop177Boundary N M (i + 1) - prop177Boundary N M i ≤ N := (Nat.sub_le _ _).trans
    (prop177_boundary_le_N (NeZero.pos N) hM (Nat.succ_le_iff.mpr i.isLt))
  have hinj : Function.Injective fun j : Fin (prop177Boundary N M (i + 1) -
      prop177Boundary N M i) => (prop177Boundary N M i : ZMod N) + (j : Nat) :=
    fun j₁ j₂ h => Fin.ext (by
      have := congrArg ZMod.val (add_left_cancel h)
      rwa [ZMod.val_natCast_of_lt (j₁.isLt.trans_le hL),
        ZMod.val_natCast_of_lt (j₂.isLt.trans_le hL)] at this)
  unfold prop177BalancedCell ModAP.IsProper modInterval ModAP.carrier
  simp only [mul_one]
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private lemma prop177_boundary_increment {N M q : Nat}
    (hN : 0 < N) (hM : 0 < M)
    (hqW : (q : Real) ≤ prop177CellWidth N M)
    (hWq : prop177CellWidth N M < q + 1)
    (i : Fin M) :
    prop177Boundary N M (i + 1) - prop177Boundary N M i = q ∨
      prop177Boundary N M (i + 1) - prop177Boundary N M i = q + 1 := by
  have hiw0 : 0 ≤ (i : Real) * prop177CellWidth N M :=
    mul_nonneg (Nat.cast_nonneg _) (prop177_width_pos hN hM).le
  have hlower : prop177Boundary N M i + q ≤ prop177Boundary N M (i + 1) := by
    rw [prop177Boundary, prop177Boundary, ← Nat.ceil_add_natCast hiw0]
    exact Nat.ceil_mono (by push_cast; linarith)
  have hupper : prop177Boundary N M (i + 1) ≤ prop177Boundary N M i + q + 1 := by
    simp only [prop177Boundary, Nat.ceil_le]
    push_cast
    linarith [Nat.le_ceil ((i : Real) * prop177CellWidth N M)]
  omega

private lemma prop177_cellIndex_intCast {N M : Nat} [NeZero N]
    (hM : 0 < M) (z : Int) :
    (((prop177CellIndex (N := N) hM (z : ZMod N) : Fin M) : Nat) : ZMod M) =
      (⌊(z : Real) / prop177CellWidth N M⌋ : ZMod M) := by
  have hN : (N : Int) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast (NeZero.pos N).ne'
  -- `z / w = (z % N) / w + M * (z / N)` with `w = N / M`
  have hdecomp : (z : Real) / prop177CellWidth N M =
      ((z % (N : Int) : Int) : Real) / prop177CellWidth N M +
        (((M : Int) * (z / (N : Int)) : Int) : Real) := by
    have hzR : (z : Real) = ((z % (N : Int) : Int) : Real) +
        (N : Real) * ((z / (N : Int) : Int) : Real) := by
      exact_mod_cast (Int.emod_add_mul_ediv z N).symm
    unfold prop177CellWidth
    rw [hzR]
    field_simp
    push_cast
    ring
  have hnonneg : 0 ≤ ((z % (N : Int) : Int) : Real) / prop177CellWidth N M :=
    div_nonneg (by exact_mod_cast Int.emod_nonneg z hN)
      (prop177_width_pos (NeZero.pos N) hM).le
  change ((⌊(((z : ZMod N).val : Nat) : Real) / prop177CellWidth N M⌋₊ : Nat) : ZMod M) = _
  rw [show (((z : ZMod N).val : Nat) : Real) = ((z % (N : Int) : Int) : Real) by
      exact_mod_cast ZMod.val_intCast z, ← Int.cast_natCast, Int.natCast_floor_eq_floor hnonneg,
    hdecomp, Int.floor_add_intCast]
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
  have hzmod : (((t.val : Int) - ∑ i, if e i then a i else 0 : Int) : ZMod N) =
      t - ∑ i, if e i then (a i : ZMod N) else 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hzmod, prop177_cellIndex_intCast hM]
  unfold floorAffinePattern
  push_cast
  rw [sub_div, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp [neg_div]

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
  simpa only [prop177RawPattern, prop177_cellIndex_floorAffine hM t a] using
    hFmem ((t.val : Real) / prop177CellWidth N M) _ ha

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
  -- a vertex outside its cell kills the product
  have hzero (g : (Fin k → Bool) → ZMod M) (c : ZMod M) (e : Fin k → Bool)
      (he : prop177RawPattern hM t a e ≠ g e + c) :
      ∏ e, parityConj e (restrictToCell (prop177ResidueCell N M (g e + c)).carrier (H e)
        (t - ∑ i, if e i then (a i : ZMod N) else 0)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
    unfold restrictToCell
    rw [if_neg (mt (prop177_mem_residueCell_iff hM _ _).mp he)]
    simp [parityConj]
  rw [Finset.sum_eq_single_of_mem _ hnorm]
  · rw [Fintype.sum_eq_single (prop177RawPattern hM t a (prop177ZeroVertex k))]
    · refine Finset.prod_congr rfl fun e _ => ?_
      have hin : (t - ∑ i, if e i then (a i : ZMod N) else 0) ∈ (prop177ResidueCell N M
          (prop177RawPattern hM t a e - prop177RawPattern hM t a (prop177ZeroVertex k) +
            prop177RawPattern hM t a (prop177ZeroVertex k))).carrier :=
        (prop177_mem_residueCell_iff hM _ _).mpr (sub_add_cancel _ _).symm
      unfold restrictToCell
      rw [if_pos hin]
    · exact fun c hc => hzero _ c (prop177ZeroVertex k) (by simpa using hc.symm)
  · intro g hgF hgne
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ∀ e, prop177RawPattern hM t a e = g e + c
    · have h0 := h (prop177ZeroVertex k)
      rw [hFzero g hgF, zero_add] at h0
      exact (hgne (funext fun e => by simp only [h e, h0, add_sub_cancel_right])).elim
    · push Not at h
      obtain ⟨e, he⟩ := h
      exact hzero g c e he

/-! ### The small-scale singleton branch -/

private lemma prop177_norm_cubeDifference_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    ‖cubeDifference f x s‖ =
      ∏ e : Fin d → Bool, ‖f (cubeArgument s x e)‖ := by
  rw [cubeDifference_eq_parity_product, norm_prod]
  apply Finset.prod_congr rfl
  intro e _
  by_cases h : Even (boolWeight e) <;> simp [parityConj, h]

private lemma prop177_cube_weight_sum (d : Nat) :
    ∑ _e : Fin d → Bool, (1 : Real) / 2 ^ d = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_one_div_cancel (by positivity)

/-- AM-GM over the vertices of a Boolean cube, with uniform weights. -/
private lemma prop177_cube_amgm {d : Nat} (z : (Fin d → Bool) → Real)
    (hz : ∀ e, 0 ≤ z e) :
    ∏ e, z e ^ ((1 : Real) / 2 ^ d) ≤ ∑ e, (1 : Real) / 2 ^ d * z e :=
  Real.geom_mean_le_arith_mean_weighted _ _ _ (fun _ _ => by positivity)
    (prop177_cube_weight_sum d) fun e _ => hz e

private lemma prop177_cube_norm_sq_le_moment {N k : Nat}
    (f : ZMod N → Complex) (x : Point N k) (s : ZMod N) :
    ‖cubeDifference f x s‖ ^ 2 ≤
      ((2 : Real) ^ k)⁻¹ *
        ∑ e : Fin k → Bool, ‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1)) := by
  have hterm (e : Fin k → Bool) :
      (‖f (cubeArgument s x e)‖ ^ ((2 : Nat) ^ (k + 1))) ^ ((1 : Real) / 2 ^ k) =
        ‖f (cubeArgument s x e)‖ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_two]
    congr 1
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    field_simp
  rw [prop177_norm_cubeDifference_product, ← Finset.prod_pow, ← one_div, Finset.mul_sum]
  simp_rw [← hterm]
  exact prop177_cube_amgm _ fun e => by positivity

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
    _ = T := by norm_num
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
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hupper : (∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2) ≤
      (m : Real) ^ k * ((N : Real) * ∑ s : ZMod N, ‖f s‖ ^ ((2 : Nat) ^ (k + 1))) :=
    (Finset.sum_le_card_nsmul _ _ _ fun x _ => prop177_fourier_sq_le_moment f x (sigma x)).trans
      (by rw [nsmul_eq_mul]; gcongr; exact_mod_cast prop177_box_card_le P haxes)
  refine le_of_mul_le_mul_left ?_ (mul_pos hN (pow_pos (Nat.cast_pos.mpr hm) k))
  linarith [henergy.trans hupper]

private lemma prop177_parity_product_succ (n : Nat) (z : Complex) :
    (∏ e : Fin (n + 1) → Bool, parityConj e z) =
      (∏ e : Fin n → Bool, parityConj e z) *
        star (∏ e : Fin n → Bool, parityConj e z) := by
  calc _ = ∏ p : Bool × (Fin n → Bool), parityConj (Fin.cons p.1 p.2 : Fin (n + 1) → Bool) z :=
        ((Fin.consEquiv fun _ : Fin (n + 1) => Bool).prod_comp (parityConj · z)).symm
    _ = _ := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool, star_prod, mul_comm]
      simp only [prop172_parityConj_cons_false, prop172_parityConj_cons_true]

private lemma prop177_parity_product_closed (n : Nat) (z : Complex) :
    (∏ e : Fin (n + 1) → Bool, parityConj e z) =
      ((‖z‖ ^ ((2 : Nat) ^ (n + 1)) : Real) : Complex) := by
  induction n with
  | zero =>
      rw [prop177_parity_product_succ]
      simp [parityConj, boolWeight, countWhere, Complex.mul_conj']
  | succ n ih =>
      rw [prop177_parity_product_succ, ih, ← starRingEnd_apply, Complex.conj_ofReal]
      push_cast
      rw [pow_succ]
      ring

private lemma prop177_singleton_cube_sum {N n : Nat} [NeZero N]
    (f : ZMod N → Complex) (t : ZMod N) :
    (∑ x : Point N (n + 1), ∑ s : ZMod N,
      cubeDifference (restrictToCell {t} f) x s) =
      ((‖f t‖ ^ ((2 : Nat) ^ (n + 1)) : Real) : Complex) := by
  -- a vertex argument other than `t` kills the product
  have hzero (x : Point N (n + 1)) (s : ZMod N) (e : Fin (n + 1) → Bool)
      (he : cubeArgument s x e ≠ t) :
      ∏ e, parityConj e (restrictToCell {t} f (cubeArgument s x e)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) (by simp [restrictToCell, he, parityConj])
  simp_rw [prop172_cubeDifference_product]
  rw [Fintype.sum_eq_single (0 : Point N (n + 1))]
  · rw [Fintype.sum_eq_single t]
    · simpa [cubeArgument, restrictToCell] using prop177_parity_product_closed n (f t)
    · exact fun s hst => hzero 0 s (prop177ZeroVertex (n + 1))
        (by simpa [cubeArgument, prop177ZeroVertex] using hst)
  · intro x hx0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hst : s = t
    · exact hzero x s (fun j => decide (j = i)) (by simpa [cubeArgument, hst] using hi)
    · exact hzero x s (prop177ZeroVertex (n + 1))
        (by simpa [cubeArgument, prop177ZeroVertex] using hst)

private def prop177SingletonCells (N : Nat) : Fin N → ModAP N :=
  fun i => modInterval N (i : ZMod N) 1

private lemma prop177_singleton_partition (N : Nat) [NeZero N] :
    IsPartition (fun i : Fin N => (prop177SingletonCells N i).carrier) Finset.univ := by
  constructor
  · intro x
    simp only [Finset.mem_univ, true_iff]
    let i : Fin N := (prop177FinZModEquiv N).symm x
    refine ⟨i, ?_⟩
    rw [prop177SingletonCells, modInterval_one_carrier, Finset.mem_singleton]
    exact (prop177FinZModEquiv N).apply_symm_apply x |>.symm
  · intro i j hij
    change Disjoint (modInterval N (i : ZMod N) 1).carrier
      (modInterval N (j : ZMod N) 1).carrier
    rw [modInterval_one_carrier, modInterval_one_carrier]
    apply Finset.disjoint_singleton.mpr
    exact fun h => bne_iff_ne.mp hij ((prop177FinZModEquiv N).injective h)

private lemma prop177_singleton_proper (N : Nat) [NeZero N] (i : Fin N) :
    (prop177SingletonCells N i).IsProper := by
  unfold ModAP.IsProper
  change (modInterval N (i : ZMod N) 1).carrier.card = 1
  rw [modInterval_one_carrier]
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
      rw [prop177SingletonCells, modInterval_one_carrier,
        prop177_singleton_cube_sum]
      simp only [prop177FinZModEquiv, Equiv.coe_fn_mk]
      rw [Complex.ofReal_re]
    _ = _ := (prop177FinZModEquiv N).sum_comp
      (fun t => ‖f t‖ ^ ((2 : Nat) ^ (k + 1)))

attribute [simp] exponential_zero

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
        (∀ i, (Q i).length ≤ m) ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1) := by
  refine ⟨fun _ => 0, N, 1, prop177SingletonCells N, ⟨fun _ => 0, fun x _ => by simp⟩,
    prop177_singleton_partition N, fun i => ⟨prop177_singleton_proper N i, Or.inl rfl⟩, ?_,
    fun _ => hm.pos, fun huniform => ?_⟩
  · rw [Nat.cast_one, div_le_one (by positivity : (0 : Real) < 3 * k)]
    exact_mod_cast hsmall
  · unfold UniformOnPartition at huniform
    rw [show phaseTwist f (fun _ => 0) = f from funext fun s => by simp [phaseTwist],
      prop177_singleton_uniform_sum] at huniform
    norm_num only [Nat.cast_one, one_add_one_eq_two, Nat.cast_ofNat] at huniform
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    linarith [prop177_energy_implies_moment f P sigma alpha hm.pos haxes henergy,
      mul_pos (sub_pos.mpr (prop177_small_coefficient_lt_one k hk)) (mul_pos halpha hN)]

/-! ### Mixed cube forms and affine phase removal -/

attribute [simp] exponential_add

attribute [simp] star_exponential

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
  simp_rw [prop177_parity_phased, Finset.prod_mul_distrib, signedCubeSum,
    ← Finset.sum_neg_distrib, prop172_exponential_sum]

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
  let T : (Fin (k + 1) → Bool) → Complex := fun E =>
    parityConj E (H (Fin.tail E) (cubeArgument s (Fin.cons y a : Point N (k + 1)) E))
  -- split the vertices of the `(k+1)`-cube by their first coordinate
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Bool).prod_comp]
  change _ = ∏ p : Bool × (Fin k → Bool), T (Fin.cons p.1 p.2)
  rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm, difference, star_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun e _ => ?_
  · simp only [T, Fin.tail_cons, prop172_parityConj_cons_false, prop172_cubeArgument_cons,
      Bool.false_eq_true, if_false, sub_zero]
    rfl
  · simp only [T, Fin.tail_cons, prop172_parityConj_cons_true, prop172_cubeArgument_cons,
      if_true]
    rfl

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
  rw [sum_point_succ, Complex.ofReal_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => (prop172_fourier_sq (fun t => ∏ e : Fin k → Bool,
    parityConj e (H e (cubeArgument t a e))) (tau a)).trans ?_
  simp only [prop177_difference_mixedProduct H a, Fin.cons_zero, Fin.tail_cons]

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
  have h (i : Fin k) : (if E i.succ then d * z i.succ + r i else 0) =
      d * (if E i.succ then z i.succ else 0) + if E i.succ then r i else 0 := by
    split_ifs <;> ring
  -- restate with this file's sum instances, so that `ring` identifies the sums below
  change d * (t - ∑ i, if E i then z i else 0) - ∑ i : Fin k, (if E i.succ then r i else 0) =
    d * t - ∑ i, if E i then
      (Fin.cons (d * z 0) (fun i => d * z i.succ + r i) : Point N (k + 1)) i else 0
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, h, Finset.sum_add_distrib, mul_sub,
    mul_add, Finset.mul_sum]
  split_ifs <;> ring

private lemma prop177_affine_phase_identity {N k : Nat}
    (d : ZMod N) (r : Point N k) (sigma : Point N k → ZMod N)
    (Phi : (Fin (k + 1) → Bool) → ZMod N → ZMod N)
    (hPhi : ∀ s x,
      x 0 * sigma (Fin.tail x) = signedCubeSum Phi s x)
    (t : ZMod N) (z : Point N (k + 1)) :
    z 0 * prop177AffineTau d r sigma (Fin.tail z) =
      signedCubeSum (prop177AffinePhase d r Phi) t z := by
  have h := hPhi (d * t)
    (Fin.cons (d * z 0) (fun i => d * (Fin.tail z) i + r i) : Point N (k + 1))
  simp only [Fin.cons_zero, Fin.tail_cons] at h
  rw [prop177AffineTau, ← mul_assoc, mul_comm (z 0), h]
  simp only [signedCubeSum, prop177AffinePhase, prop177_affine_vertex_argument]

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
  ext x
  simp only [Box.carrier, ModAP.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, P.axis_step]
  constructor
  · intro hx
    choose j hj using hx
    exact ⟨fun i => Fin.cast (haxes i) (j i), funext hj⟩
  · rintro ⟨u, rfl⟩ i
    exact ⟨Fin.cast (haxes i).symm (u i), rfl⟩

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
  rw [hsum, mul_sub, Finset.mul_sum]
  have hmul :
      (∑ i : Fin k, if e i then d * a i else 0) =
        ∑ i : Fin k, d * (if e i then a i else 0) := by norm_num
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
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, prop172_cubeDifference_product]
  -- substitute `s = d * t` and write the box point as an affine image of the centred point
  refine (Fintype.sum_bijective _ (mulLeft_bijective₀ _ (bne_iff_ne.mp hd)) _ _
    fun t => ?_).symm
  simp only [funext (prop177_boxPoint_affine (h := h) P u), prop177_affine_cubeArgument]
  exact congrArg₂ (· * ·) (congrArg exponential (by unfold prop177AffineTau; ring)) rfl

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
  rw [prop177_fourier_boxPoint (h := h) f P sigma hd u]
  simp_rw [prop177_support_decomposition hM F hFzero
    (prop177ShiftedVertex f P.commonDiff (prop177BoxCenter P h)) _ _
    (prop177_normalized_raw_mem hM F hFmem _ _ ha), Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_comm

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
  obtain ⟨g, hgF, hgmax⟩ := Finset.exists_max_image F
    (fun g => ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2) hF
  refine ⟨g, hgF, hA.trans ?_⟩
  calc ∑ u : U, ‖∑ g ∈ F, ∑ c : C, V g c u‖ ^ 2
      ≤ ∑ u : U, (F.card : Real) * ∑ g ∈ F,
          (Fintype.card C : Real) * ∑ c : C, ‖V g c u‖ ^ 2 := by
        gcongr with u
        refine (prop177_norm_sum_sq_le_card F _).trans ?_
        gcongr with g
        simpa only [Finset.card_univ] using
          prop177_norm_sum_sq_le_card Finset.univ fun c => V g c u
    _ = (F.card : Real) * Fintype.card C * ∑ g ∈ F, ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
    _ ≤ (F.card : Real) * Fintype.card C * ∑ _g ∈ F, ∑ u : U, ∑ c : C, ‖V g c u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hgmax) (by positivity)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

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
  have hform : cubeForm (prop177PhasedFamily (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi)) =
      ((∑ a : Point N k, ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2 : Real) : Complex) :=
    (prop177_cubeForm_phased (prop177ExtendedLocalFamily hM f d r g c) _ _
      (prop177_affine_phase_identity d r sigma Phi hPhi)).trans
      (prop177_mixedEnergy_expansion (fun e => restrictToCell
        (prop177ResidueCell N M (g e + c)).carrier (prop177ShiftedVertex f d r e))
        (prop177AffineTau d r sigma)).symm
  rw [hform, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

attribute [simp] cor57_norm_exponential

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
  rw [norm_mul, cor57_norm_exponential, mul_one]
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
  let G : ZMod M → (Fin (k + 1) → Bool) → Real := fun c E =>
    ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool => prop177PhasedFamily
      (prop177ExtendedLocalFamily hM f d r g c) (prop177AffinePhase d r Phi) E)‖
  -- Gowers--Cauchy--Schwarz, then AM-GM over the vertices, for each cell shift `c`
  have hper (c : ZMod M) : (∑ a : Point N k, ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2) ≤
      ∑ E, (1 : Real) / 2 ^ (k + 1) * G c E := by
    rw [← prop177_local_energy_eq_cubeForm_norm hM f d r sigma g c Phi hPhi]
    exact (lemma_3_8_holds N (k + 1) _ fun E =>
      prop177_local_phased_discValued hM f hf d r g c Phi E).trans
        (prop177_cube_amgm (G c) fun E => norm_nonneg _)
  have htotal : (∑ a : Point N k, ∑ c : ZMod M,
      ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2) ≤
      ∑ E, (1 : Real) / 2 ^ (k + 1) * ∑ c, G c E := by
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun c _ => hper c).trans_eq ?_
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  -- a weighted average is at most the largest term
  obtain ⟨E, -, hE⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (f := fun _ => (1 : Real) / 2 ^ (k + 1) *
      ∑ a : Point N k, ∑ c : ZMod M, ‖prop177LocalInner hM f d r sigma g c a‖ ^ 2)
    (g := fun E => (1 : Real) / 2 ^ (k + 1) * ∑ c, G c E)
    (by simpa only [← Finset.sum_mul, prop177_cube_weight_sum, one_mul] using htotal)
  exact ⟨E, le_of_mul_le_mul_left hE (by positivity)⟩

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
  unfold prop177MapCell ModAP.carrier
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun i => ⟨fun h => mul_left_cancel₀ hd (by linear_combination h),
    fun h => by linear_combination d * h⟩

def prop177AffineEquiv {N : Nat} [NeZero N] [Fact N.Prime]
    (d offset : ZMod N) (hd : d ≠ 0) : ZMod N ≃ ZMod N :=
  (Equiv.mulLeft₀ d hd).trans (Equiv.subRight offset)

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
        ∑ i : Fin q, d * (if e i then x i else 0) := by norm_num
  rw [hsum, mul_sub, Finset.mul_sum]
  ring

private lemma prop177_constantCubeForm_affine {N q : Nat} [NeZero N]
    [Fact N.Prime] (d offset : ZMod N) (hd : d ≠ 0)
    (h : ZMod N → Complex) :
    cubeForm (d := q) (fun _ : Fin q → Bool =>
      fun u => h (d * u - offset)) =
      cubeForm (d := q) (fun _ : Fin q → Bool => h) := by
  symm
  unfold cubeForm
  rw [← (Equiv.piCongrRight fun _ : Fin q => Equiv.mulLeft₀ d hd).sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← (prop177AffineEquiv d offset hd).sum_comp]
  exact Finset.sum_congr rfl fun s _ => Finset.prod_congr rfl fun e _ =>
    congrArg (fun w => parityConj e (h w)) (prop177_cubeArgument_affine d offset s x e)

private lemma prop177_constantCubeForm_norm_eq_real_sum
    {N k : Nat} [NeZero N] (h : ZMod N → Complex) :
    ‖cubeForm (d := k + 1) (fun _ : Fin (k + 1) → Bool => h)‖ =
      ∑ x : Point N (k + 1), ∑ s : ZMod N,
        (cubeDifference h x s).re := by
  rw [constant_cubeForm_eq_sum_cubeDifference, sum_cube_succ_eq_sum_norm_sq h, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · simpa only [Complex.ofReal_re, Complex.re_sum] using
      (congrArg Complex.re (sum_cube_succ_eq_sum_norm_sq (n := k) h)).symm
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

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
  let hOrig := restrictToCell (prop177MapCell d (prop177TailOffset r E)
    (prop177ResidueCell N M (g (Fin.tail E) + c))).carrier (phaseTwist f (Phi E))
  -- the selected vertex function is the transported cell restriction, read at `d * u - offset`
  have hfun : prop177PhasedFamily (prop177ExtendedLocalFamily hM f d r g c)
      (prop177AffinePhase d r Phi) E = fun u => hOrig (d * u - prop177TailOffset r E) := by
    funext u
    simp only [hOrig, prop177PhasedFamily, prop177ExtendedLocalFamily, prop177ShiftedVertex,
      prop177AffinePhase, restrictToCell, phaseTwist, prop177_mapCell_mem_iff d _ hd,
      show prop177Offset r (Fin.tail E) = prop177TailOffset r E from rfl, ite_mul, zero_mul]
  rw [hfun, prop177_constantCubeForm_affine d _ hd hOrig]
  exact prop177_constantCubeForm_norm_eq_real_sum hOrig

private def prop177OutputCell (N M : Nat) (d offset : ZMod N)
    (i : Fin M) : ModAP N :=
  prop177MapCell d offset (prop177BalancedCell N M i)

private lemma prop177_mapCell_carrier {N : Nat} [NeZero N]
    [Fact N.Prime] (d offset : ZMod N) (hd : d ≠ 0) (Q : ModAP N) :
    (prop177MapCell d offset Q).carrier =
      Q.carrier.image (fun u => d * u - offset) := by
  ext x
  let e := prop177AffineEquiv d offset hd
  let u := e.symm x
  have heu : d * u - offset = x := e.apply_symm_apply x
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
  -- `x` lies in output cell `i` exactly when its affine preimage lies in balanced cell `i`
  have hmem (i : Fin M) (x : ZMod N) : x ∈ (prop177OutputCell N M d offset i).carrier ↔
      prop177CellIndex hM ((prop177AffineEquiv d offset hd).symm x) = i := by
    conv_lhs => rw [← (prop177AffineEquiv d offset hd).apply_symm_apply x]
    exact (prop177_mapCell_mem_iff d offset hd _ _).trans
      (prop177_balancedCell_mem_iff_index hM i _)
  exact ⟨fun x => ⟨fun _ => ⟨_, (hmem _ x).mpr rfl⟩, fun _ => Finset.mem_univ x⟩,
    fun i j hij => Finset.disjoint_left.mpr fun x hxi hxj =>
      bne_iff_ne.mp hij (((hmem i x).mp hxi).symm.trans ((hmem j x).mp hxj))⟩

private lemma prop177_output_proper {N M : Nat} [NeZero N]
    [Fact N.Prime] (hM : 0 < M) (d offset : ZMod N) (hd : d ≠ 0)
    (i : Fin M) : (prop177OutputCell N M d offset i).IsProper := by
  unfold ModAP.IsProper prop177OutputCell
  rw [prop177_mapCell_carrier d offset hd, Finset.card_image_iff.mpr]
  · exact prop177_balancedCell_isProper hM i
  · intro x _ y _ hxy
    exact (prop177AffineEquiv d offset hd).injective hxy

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
  let A : ZMod M → Real := fun j => ∑ x : Point N (k + 1), ∑ s : ZMod N,
    (cubeDifference (restrictToCell (prop177MapCell d (prop177TailOffset r E)
      (prop177ResidueCell N M j)).carrier (phaseTwist f (Phi E))) x s).re
  calc _ = ∑ c : ZMod M, A (g (Fin.tail E) + c) := Finset.sum_congr rfl fun c _ =>
        prop177_selected_constant_form_transport hM f d hd r g c Phi E
    _ = ∑ i : Fin M, A (prop177FinZModEquiv M i) :=
        (Equiv.sum_comp (Equiv.addLeft (g (Fin.tail E))) A).trans
          ((prop177FinZModEquiv M).sum_comp A).symm
    _ = _ := Finset.sum_congr rfl fun i _ => by
        simp only [A, prop177OutputCell, prop177ResidueCell, Equiv.symm_apply_apply]

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
  have hh : 0 < h := by omega
  have hqh : prop177Scale h k ≤ h :=
    Nat.ceil_le.mpr (div_le_self (by positivity) (by exact_mod_cast hk))
  refine ⟨Nat.ceil_pos.mpr (by positivity), by omega,
    (Nat.mul_self_le_mul_self (by omega : prop177Scale h k ≤ 2 * h + 1)).trans
      (by rw [← sq]; exact_mod_cast hSq),
    (?_ : _ ≤ (h : Real) / k).trans (Nat.le_ceil _)⟩
  have h1 : (1 : Real) ≤ h := by exact_mod_cast hh
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < 3 * k) (by positivity : (0 : Real) < k)]
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := Real) k) (sub_nonneg.mpr h1)]

private lemma prop177_quotient_width_bounds {N q : Nat}
    (hq : 0 < q) (hqSq : q * q ≤ N) :
    let M := N / q
    0 < M ∧ q ≤ M ∧
      (q : Real) ≤ prop177CellWidth N M ∧
      prop177CellWidth N M < q + 1 := by
  dsimp only
  have hqM : q ≤ N / q := (Nat.le_div_iff_mul_le hq).mpr hqSq
  have hM : (0 : Real) < (N / q : Nat) := by exact_mod_cast hq.trans_le hqM
  refine ⟨hq.trans_le hqM, hqM, ?_, ?_⟩ <;> unfold prop177CellWidth
  · rw [le_div_iff₀ hM]
    exact_mod_cast Nat.mul_div_le N q
  · rw [div_lt_iff₀ hM]
    exact_mod_cast (show N < (q + 1) * (N / q) by
      nlinarith [Nat.lt_div_mul_add (a := N) hq])

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
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by
    simp [h0, prop177CellWidth] at hqW
    omega
  have hw := prop177_width_pos hN hM
  -- `|centered| ≤ h ≤ k * w < (k + 1) * w`
  have hhW : (h : Real) ≤ k * prop177CellWidth N M := by
    linarith [(div_le_iff₀ (by exact_mod_cast hk : (0 : Real) < k)).mp hqLower,
      mul_le_mul_of_nonneg_left hqW (Nat.cast_nonneg (α := Real) k)]
  obtain ⟨hzL, hzU⟩ := prop177_centered_int_bounds u i
  norm_num only [Nat.cast_add, Nat.cast_one]
  constructor
  · rw [lt_div_iff₀ hw]
    linarith
  · rw [div_lt_iff₀ hw]
    linarith

private lemma prop177_pattern_coefficient_lt_quarter (k : Nat) (hk : 0 < k) :
    (((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2) *
        (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) < 1 / 4 := by
  have h : 4 * (2 ^ (k * (k + 1) ^ 2)) ^ 2 < 2 ^ (2 * (k + 1) ^ 3) :=
    calc 4 * (2 ^ (k * (k + 1) ^ 2)) ^ 2 = 2 ^ (2 + 2 * (k * (k + 1) ^ 2)) := by ring
      _ < 2 ^ (2 * (k + 1) ^ 3) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith [mul_pos hk hk])
  have hR : (4 : Real) * ((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2 <
      (2 : Real) ^ (2 * (k + 1) ^ 3) := by exact_mod_cast h
  rw [show (2 * (k + 1) ^ 3 : Int) = (2 * (k + 1) ^ 3 : Nat) by norm_num, zpow_neg, zpow_natCast,
    ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

private lemma prop177_quantitative_strict
    {N k m q M : Nat} (alpha S : Real)
    (halpha : 0 < alpha) (hk : 0 < k) (hq : 0 < q) (hM : 0 < M)
    (hqMleN : q * M ≤ N) (hqm : q + 1 ≤ m)
    (hraw : alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      (((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2) * M * S) :
    (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha *
        ((q + 1 : Nat) : Real) ^ (k + 2) * M < S := by
  have hq2 : ((q + 1 : Nat) : Real) ≤ 2 * q := by exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have hqm' : ((q + 1 : Nat) : Real) ≤ m := by exact_mod_cast hqm
  have hqM : (q : Real) * M ≤ N := by exact_mod_cast hqMleN
  -- multiply by `L ^ 2 * M`, where `L ^ 2 * 2 ^ (-2 (k + 1) ^ 3) < 1 / 4`
  refine lt_of_mul_lt_mul_left (lt_of_lt_of_le ?_ hraw) (by positivity)
  calc _ = ((((2 ^ (k * (k + 1) ^ 2) : Nat) : Real) ^ 2) *
          (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int))) *
        (alpha * (((q + 1 : Nat) : Real) ^ 2 * ((q + 1 : Nat) : Real) ^ k * (M : Real) ^ 2)) := by
        ring
    _ < 1 / 4 * (alpha * ((2 * (q : Real)) ^ 2 * (m : Real) ^ k * (M : Real) ^ 2)) :=
      mul_lt_mul (prop177_pattern_coefficient_lt_quarter k hk) (by gcongr) (by positivity)
        (by norm_num)
    _ = alpha * (((q : Real) * M) ^ 2 * (m : Real) ^ k) := by ring
    _ ≤ alpha * ((N : Real) ^ 2 * (m : Real) ^ k) := by gcongr
    _ = alpha * (N : Real) ^ 2 * (m : Real) ^ k := by ring

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
        (∀ i, (Q i).length ≤ 2 * h + 1) ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1) := by
  have hmSq : (((2 * h + 1 : Nat) : Real) ^ 2) ≤ (N : Real) :=
    (Real.le_sqrt' (by positivity)).mp hmsqrt
  have hmN : 2 * h + 1 ≤ N := (Nat.le_self_pow two_ne_zero _).trans (by exact_mod_cast hmSq)
  have hkN : k + 1 < N := by omega
  have hd' : P.commonDiff ≠ 0 := bne_iff_ne.mp hd
  let q := prop177Scale h k
  obtain ⟨hqpos, hqSucc, hqSq, hlower⟩ := prop177_scale_bounds (N := N) hk hlarge hmSq
  let M := N / q
  obtain ⟨hMpos, _, hqWidth, hWidthUpper⟩ :=
    prop177_quotient_width_bounds (N := N) (q := q) hqpos hqSq
  letI : NeZero M := ⟨hMpos.ne'⟩
  obtain ⟨F, hFcard, hFzero, hFmem⟩ := prop177_exists_normalized_mod_patterns k M hk
  have hk1 : (0 : Real) < ((k + 1 : Nat) : Real) := by positivity
  -- localize the energy to the patterns `g ∈ F` and select one pattern
  obtain ⟨g, _, hgSelect⟩ := prop177_select_double_sum F
    ⟨_, hFmem 0 (fun _ => 0) fun _ => ⟨neg_lt_zero.mpr hk1, hk1⟩⟩
    (fun g c (u : prop177BoxParameter k (2 * h + 1)) => prop177LocalInner hMpos f
      P.commonDiff (prop177BoxCenter P h) sigma g c (prop177CenteredPoint h u)) _
    (henergy.trans_eq ((prop177_energy_reindex_box f P sigma haxes hd hmN).trans
      (Finset.sum_congr rfl fun u _ => by
        rw [prop177_fourier_eq_localized_sum (h := h) hMpos f P sigma hd F hFzero hFmem u
          (prop177_centered_coefficient_bound hk hMpos hqpos (Nat.le_ceil ((h : Real) / k))
            hqWidth u)])))
  simp only [ZMod.card] at hgSelect
  -- remove the phase and select one vertex of the cube
  obtain ⟨Phi, hPhiPoly, hPhi⟩ := lemma_17_1_holds N (k + 1) hkN
    (prop177_factorial_unit hkN) _ (prop172_multilinear_cons sigma hsigma)
  obtain ⟨E, hVertex⟩ := prop177_select_local_vertex hMpos f hf P.commonDiff
    (prop177BoxCenter P h) sigma g Phi hPhi
  let Q := prop177OutputCell N M P.commonDiff (prop177TailOffset (prop177BoxCenter P h) E)
  have hlen (i : Fin M) : (Q i).length = q ∨ (Q i).length = q + 1 :=
    prop177_boundary_increment (NeZero.pos N) hMpos hqWidth hWidthUpper i
  refine ⟨Phi E, M, q, Q, hPhiPoly E, prop177_output_partition hMpos _ _ hd',
    fun i => ⟨prop177_output_proper hMpos _ _ hd' i, hlen i⟩, hlower,
    fun i => by have := hlen i; omega, fun hU => ?_⟩
  unfold UniformOnPartition at hU
  simp_rw [prop177_double_sum_re] at hU
  refine not_lt.mpr hU (prop177_quantitative_strict (M := M) alpha _ halpha hk hqpos hMpos
    (Nat.mul_div_le N q) hqSucc (hgSelect.trans (mul_le_mul (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hFcard) 2) (by positivity)) ?_
      (by positivity) (by positivity))))
  exact (prop177_sum_centered_le_univ (h := h) hmN (fun a => ∑ c : ZMod M,
    ‖prop177LocalInner hMpos f P.commonDiff (prop177BoxCenter P h) sigma g c a‖ ^ 2)
    fun _ => by positivity).trans (hVertex.trans_eq (prop177_transport_sum_reindex hMpos f
      P.commonDiff hd' (prop177BoxCenter P h) g Phi E))

/-- The actual phase-removal construction also retains an upper bound on
 every output cell, needed for subsequent no-wrap energy transport. -/
theorem proposition_17_7_with_upper :
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
      (P : Box N k) (sigma : Point N k → ZMod N) (alpha : Real),
    0 < alpha → 0 < k → Odd m → P.width = m →
    (∀ i, (P.axis i).length = m) → P.commonDiff != 0 →
    (m : Real) ≤ Real.sqrt N → DiscValued f → IsMultilinear sigma →
    alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 →
    ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
      PolynomialOn (k + 1) Finset.univ phi ∧
      IsPartition (fun i => (Q i).carrier) Finset.univ ∧
      (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
      (m : Real) / (3 * k) ≤ l ∧ (∀ i, (Q i).length ≤ m) ∧
      ¬ UniformOnPartition (phaseTwist f phi) k
        ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1) := by
  intro N k m _ _ f P sigma alpha halpha hk hm _ haxes hd hmsqrt hf hsigma henergy
  rcases le_or_gt m (3 * k) with hsmall | hlarge
  · exact prop177_small_branch f P sigma alpha halpha hk hm haxes henergy hsmall
  · obtain ⟨h, rfl⟩ := hm
    exact prop177_large_branch f P sigma alpha halpha hk hlarge haxes hd hmsqrt hf hsigma henergy

end LeanProofs.GowersSzemeredi
