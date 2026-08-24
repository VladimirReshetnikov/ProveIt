import GowersSzemeredi.Sections17_18
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite floor patterns in Section 17

This file proves Corollaries 17.5 and 17.6.  The finite family in the first
corollary is obtained from the sign patterns of the finitely many integer
threshold hyperplanes which can meet the bounded coefficient box.  A
Sauer--Shelah argument bounds those sign patterns.  The second corollary
separates the integer and fractional parts of the affine constant.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### A finite-dimensional sign-pattern bound -/

/-- Sets cut out by strict homogeneous linear inequalities. -/
private def linearSignFamily {d : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin d → Real) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun u =>
    ∃ w : Fin d → Real, ∀ i, i ∈ u ↔ (∑ j, v i j * w j) < 0

/-- A homogeneous linear sign family in dimension `d` cannot shatter more
than `d` points. -/
private lemma linearSignFamily_shattered_card_le {d : Nat} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → Fin d → Real) (s : Finset ι)
    (hs : (linearSignFamily v).Shatters s) : s.card ≤ d := by
  classical
  by_contra hsd
  have hd_lt : d < Fintype.card s := by
    simpa only [Fintype.card_coe] using Nat.lt_of_not_ge hsd
  have hdep : ¬ LinearIndependent Real (fun i : s => v i.1) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at this
    exact (Nat.not_le_of_lt hd_lt) this
  obtain ⟨c0, hc0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let c : s → Real := if 0 < c0 i0 then c0 else -c0
  have hc : ∑ i, c i • v i.1 = 0 := by
    by_cases hpos : 0 < c0 i0
    · simpa [c, hpos] using hc0
    · have hneg : c = -c0 := by simp [c, hpos]
      rw [hneg]
      simp_rw [Pi.neg_apply, neg_smul]
      rw [Finset.sum_neg_distrib, hc0, neg_zero]
  have hi0pos : 0 < c i0 := by
    by_cases hpos : 0 < c0 i0
    · simp [c, hpos]
    · have hle : c0 i0 ≤ 0 := le_of_not_gt hpos
      have hlt : c0 i0 < 0 := lt_of_le_of_ne hle hi0
      simpa [c, hpos] using neg_pos.mpr hlt
  let t : Finset ι := (s.attach.filter fun i => 0 < c i).image Subtype.val
  have hts : t ⊆ s := by
    intro i hi
    simp only [t, mem_image, mem_filter, mem_attach] at hi
    obtain ⟨j, ⟨_, _⟩, rfl⟩ := hi
    exact j.2
  obtain ⟨u, hu, hsu⟩ := hs hts
  rw [linearSignFamily, mem_filter] at hu
  obtain ⟨w, hw⟩ := hu.2
  have hmem (i : s) : i.1 ∈ u ↔ 0 < c i := by
    have his : i.1 ∈ s := i.2
    calc
      i.1 ∈ u ↔ i.1 ∈ s ∩ u := by simp [his]
      _ ↔ i.1 ∈ t := by rw [hsu]
      _ ↔ 0 < c i := by simp [t]
  have hterm (i : s) : c i * (∑ j, v i.1 j * w j) ≤ 0 := by
    by_cases hci : 0 < c i
    · exact mul_nonpos_of_nonneg_of_nonpos hci.le (hw i.1 |>.mp (hmem i |>.mpr hci)).le
    · have hdot : 0 ≤ ∑ j, v i.1 j * w j := by
        exact le_of_not_gt fun hlt => hci ((hmem i).mp ((hw i.1).mpr hlt))
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hci) hdot
  have hterm0 : c i0 * (∑ j, v i0.1 j * w j) < 0 :=
    mul_neg_of_pos_of_neg hi0pos ((hw i0.1).mp ((hmem i0).mpr hi0pos))
  have hsumneg : (∑ i : s, c i * (∑ j, v i.1 j * w j)) < 0 := by
    simpa only [Finset.sum_const_zero] using
      Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hterm i) ⟨i0, mem_univ _, hterm0⟩
  have hsumzero : (∑ i : s, c i * (∑ j, v i.1 j * w j)) = 0 := by
    calc
      (∑ i : s, c i * (∑ j, v i.1 j * w j)) =
          ∑ j, (∑ i : s, c i * v i.1 j) * w j := by
            simp_rw [Finset.mul_sum, ← mul_assoc]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
      _ = 0 := by
        have hcj (j : Fin d) : ∑ i : s, c i * v i.1 j = 0 := by
          have := congrFun hc j
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
        apply Finset.sum_eq_zero
        intro j _
        rw [hcj j, zero_mul]
  rw [hsumzero] at hsumneg
  exact lt_irrefl 0 hsumneg

private lemma linearSignFamily_vcDim_le {d : Nat} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → Fin d → Real) :
    (linearSignFamily v).vcDim ≤ d := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro s hs
  exact linearSignFamily_shattered_card_le v s (Finset.mem_shatterer.mp hs)

private lemma sum_range_pow_le_two_mul_pow (n d : Nat) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (d + 1), n ^ j) ≤ 2 * n ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hstep : 2 * n ^ d ≤ n ^ (d + 1) := by
        rw [pow_succ]
        nlinarith [Nat.zero_le (n ^ d)]
      calc
        (∑ j ∈ Finset.range (d + 1), n ^ j) + n ^ (d + 1) ≤
            2 * n ^ d + n ^ (d + 1) := Nat.add_le_add_right ih _
        _ ≤ n ^ (d + 1) + n ^ (d + 1) := Nat.add_le_add_right hstep _
        _ = 2 * n ^ (d + 1) := by omega

/-- Coarse Sauer--Shelah bound sufficient for the published exponent. -/
private lemma linearSignFamily_card_le {d : Nat} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → Fin d → Real)
    (hcard : 2 ≤ Fintype.card ι) :
    (linearSignFamily v).card ≤ 2 * (Fintype.card ι) ^ d := by
  classical
  let A := linearSignFamily v
  have hvc : A.vcDim ≤ d := linearSignFamily_vcDim_le v
  have hIic : Finset.Iic A.vcDim ⊆ Finset.Iic d := by
    intro j hj
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hj).trans hvc)
  have hIic_range : Finset.Iic d = Finset.range (d + 1) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  calc
    A.card ≤ A.shatterer.card := Finset.card_le_card_shatterer A
    _ ≤ ∑ j ∈ Finset.Iic A.vcDim, (Fintype.card ι).choose j :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ j ∈ Finset.Iic d, (Fintype.card ι).choose j :=
      Finset.sum_le_sum_of_subset hIic
    _ = ∑ j ∈ Finset.range (d + 1), (Fintype.card ι).choose j := by rw [hIic_range]
    _ ≤ ∑ j ∈ Finset.range (d + 1), (Fintype.card ι) ^ j := by
      exact Finset.sum_le_sum fun j _ => Nat.choose_le_pow _ _
    _ ≤ 2 * (Fintype.card ι) ^ d :=
      sum_range_pow_le_two_mul_pow _ _ hcard

/-! ### Integer threshold patterns -/

private def coefficientBound {k : Nat} (r : Nat) (alpha : Fin k → Real) : Prop :=
  ∀ i, -(r : Real) < alpha i ∧ alpha i < r

private def subsetSum {k : Nat} (alpha : Fin k → Real) (e : Fin k → Bool) : Real :=
  ∑ i, if e i then alpha i else 0

private abbrev ThresholdQuery (k R : Nat) :=
  (Fin k → Bool) × ↥(Finset.Icc (-(R : Int)) (R : Int))

private def thresholdPattern {k R : Nat} (alpha : Fin k → Real) :
    Finset (ThresholdQuery k R) :=
  Finset.univ.filter fun q => subsetSum alpha q.1 < (q.2.1 : Real)

private def thresholdVector {k R : Nat} (q : ThresholdQuery k R) :
    Fin (k + 1) → Real :=
  Fin.lastCases (-(q.2.1 : Real)) (fun i => if q.1 i then 1 else 0)

private def thresholdWitness {k : Nat} (alpha : Fin k → Real) : Fin (k + 1) → Real :=
  Fin.lastCases 1 alpha

private lemma threshold_dot {k R : Nat} (q : ThresholdQuery k R)
    (alpha : Fin k → Real) :
    (∑ j, thresholdVector q j * thresholdWitness alpha j) =
      subsetSum alpha q.1 - (q.2.1 : Real) := by
  rw [Fin.sum_univ_castSucc]
  simp only [thresholdVector, thresholdWitness, Fin.lastCases_castSucc, Fin.lastCases_last,
    subsetSum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases q.1 i <;> simp
  · ring

private lemma thresholdPattern_mem_linearSignFamily {k R : Nat}
    (alpha : Fin k → Real) :
    thresholdPattern (R := R) alpha ∈ linearSignFamily thresholdVector := by
  classical
  rw [linearSignFamily, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, thresholdWitness alpha, ?_⟩
  intro q
  rw [thresholdPattern, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, threshold_dot]
  constructor <;> intro h <;> linarith

private def boundedThresholdFamily (k r : Nat) :
    Finset (Finset (ThresholdQuery k (r * k))) := by
  classical
  exact Finset.univ.filter fun u =>
    ∃ alpha : Fin k → Real,
      coefficientBound r alpha ∧ thresholdPattern (R := r * k) alpha = u

private lemma boundedThresholdFamily_subset_linear (k r : Nat) :
    boundedThresholdFamily k r ⊆ linearSignFamily thresholdVector := by
  classical
  intro u hu
  rw [boundedThresholdFamily, Finset.mem_filter] at hu
  obtain ⟨alpha, _, rfl⟩ := hu.2
  exact thresholdPattern_mem_linearSignFamily alpha

private def thresholdRepresentative (k r : Nat) (u : ↥(boundedThresholdFamily k r)) :
    Fin k → Real := by
  classical
  exact Classical.choose (Finset.mem_filter.mp u.2).2

private lemma thresholdRepresentative_bound (k r : Nat)
    (u : ↥(boundedThresholdFamily k r)) :
    coefficientBound r (thresholdRepresentative k r u) := by
  classical
  exact (Classical.choose_spec (Finset.mem_filter.mp u.2).2).1

private lemma thresholdRepresentative_pattern (k r : Nat)
    (u : ↥(boundedThresholdFamily k r)) :
    thresholdPattern (R := r * k) (thresholdRepresentative k r u) = u.1 := by
  classical
  exact (Classical.choose_spec (Finset.mem_filter.mp u.2).2).2

private lemma subsetSum_bounds {k r : Nat} (hk : 0 < k) (hr : 0 < r)
    (alpha : Fin k → Real) (ha : coefficientBound r alpha) (e : Fin k → Bool) :
    -(r * k : Nat) < subsetSum alpha e ∧ subsetSum alpha e < r * k := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  constructor
  · calc
      -(r * k : Nat) = ∑ _i : Fin k, -(r : Real) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul]
        ring
      _ < ∑ i : Fin k, (if e i then alpha i else 0) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        cases e i <;> simp [ha i, hr]
      _ = subsetSum alpha e := rfl
  · calc
      subsetSum alpha e = ∑ i : Fin k, (if e i then alpha i else 0) := rfl
      _ < ∑ _i : Fin k, (r : Real) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        cases e i <;> simp [ha i, hr]
      _ = r * k := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma floorDotPattern_eq_of_thresholdPattern_eq {k r : Nat}
    (hk : 0 < k) (hr : 0 < r) (alpha beta : Fin k → Real)
    (ha : coefficientBound r alpha) (hb : coefficientBound r beta)
    (heq : thresholdPattern (R := r * k) alpha = thresholdPattern (R := r * k) beta) :
    floorDotPattern alpha = floorDotPattern beta := by
  funext e
  let x := subsetSum alpha e
  let y := subsetSum beta e
  have hx := subsetSum_bounds hk hr alpha ha e
  have hy := subsetSum_bounds hk hr beta hb e
  apply le_antisymm
  · by_contra hxy
    have hyx : ⌊y⌋ < ⌊x⌋ := lt_of_not_ge hxy
    have hzmem : ⌊x⌋ ∈ Finset.Icc (-(r * k : Nat) : Int) (r * k : Nat) := by
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_floor.mpr
        simpa [x, Nat.cast_mul] using (le_of_lt hx.1)
      · apply (Int.floor_lt.mpr ?_).le
        simpa [x, Nat.cast_mul] using hx.2
    let q : ThresholdQuery k (r * k) := ⟨e, ⟨⌊x⌋, hzmem⟩⟩
    have hqx : q ∉ thresholdPattern (R := r * k) alpha := by
      rw [thresholdPattern, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, q, x]
      exact not_lt_of_ge (Int.floor_le (subsetSum alpha e))
    have hqy : q ∈ thresholdPattern (R := r * k) beta := by
      rw [thresholdPattern, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, q, x]
      exact Int.floor_lt.mp hyx
    rw [heq] at hqx
    exact hqx hqy
  · by_contra hyx
    have hxy : ⌊x⌋ < ⌊y⌋ := lt_of_not_ge hyx
    have hzmem : ⌊y⌋ ∈ Finset.Icc (-(r * k : Nat) : Int) (r * k : Nat) := by
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_floor.mpr
        simpa [y, Nat.cast_mul] using (le_of_lt hy.1)
      · apply (Int.floor_lt.mpr ?_).le
        simpa [y, Nat.cast_mul] using hy.2
    let q : ThresholdQuery k (r * k) := ⟨e, ⟨⌊y⌋, hzmem⟩⟩
    have hqy : q ∉ thresholdPattern (R := r * k) beta := by
      rw [thresholdPattern, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, q, y]
      exact not_lt_of_ge (Int.floor_le (subsetSum beta e))
    have hqx : q ∈ thresholdPattern (R := r * k) alpha := by
      rw [thresholdPattern, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, q, y]
      exact Int.floor_lt.mp hxy
    rw [← heq] at hqy
    exact hqy hqx

private lemma thresholdQuery_card (k R : Nat) :
    Fintype.card (ThresholdQuery k R) = 2 ^ k * (2 * R + 1) := by
  simp only [ThresholdQuery, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_coe, Int.card_Icc]
  congr 1
  rw [sub_neg_eq_add]
  rw [Int.toNat_add (by omega) (by omega)]
  rw [Int.toNat_add (by omega) (by omega)]
  omega

private lemma two_mul_add_one_le_two_pow_succ (a : Nat) (ha : 1 ≤ a) :
    2 * a + 1 ≤ 2 ^ (a + 1) := by
  induction a with
  | zero => omega
  | succ a ih =>
      by_cases h : a = 0
      · subst a
        norm_num
      · have ha' : 1 ≤ a := by omega
        have ih' := ih ha'
        rw [pow_succ]
        omega

private lemma thresholdQuery_card_le_pow (k r : Nat) (hrk : 1 ≤ r * k) :
    Fintype.card (ThresholdQuery k (r * k)) ≤ 2 ^ (k + r * k + 1) := by
  rw [thresholdQuery_card]
  calc
    2 ^ k * (2 * (r * k) + 1) ≤ 2 ^ k * 2 ^ (r * k + 1) :=
      Nat.mul_le_mul_left _ (two_mul_add_one_le_two_pow_succ _ hrk)
    _ = 2 ^ (k + r * k + 1) := by rw [← pow_add, Nat.add_assoc]

private lemma finitePattern_exponent_bound (k r : Nat) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    1 + (k + r * k + 1) * (k + 1) ≤ 2 * r * k ^ 3 := by
  have hbase : 1 + (k + k + 1) * (k + 1) ≤ 2 * k ^ 3 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    ring_nf
    omega
  have hslope : k * (k + 1) ≤ 2 * k ^ 3 := by
    have hk1 : k + 1 ≤ 2 * k ^ 2 := by
      nlinarith [sq_nonneg (k : Int)]
    calc
      k * (k + 1) ≤ k * (2 * k ^ 2) := Nat.mul_le_mul_left k hk1
      _ = 2 * k ^ 3 := by ring
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  calc
    1 + (k + (1 + s) * k + 1) * (k + 1) =
        (1 + (k + k + 1) * (k + 1)) + s * (k * (k + 1)) := by ring
    _ ≤ 2 * k ^ 3 + s * (2 * k ^ 3) :=
      Nat.add_le_add hbase (Nat.mul_le_mul_left s hslope)
    _ = 2 * (1 + s) * k ^ 3 := by ring

private lemma boundedThresholdFamily_card_le (k r : Nat) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    (boundedThresholdFamily k r).card ≤ 2 ^ (2 * r * k ^ 3) := by
  classical
  let Qcard := Fintype.card (ThresholdQuery k (r * k))
  have hrk : 1 ≤ r * k :=
    Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hr) (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hQ : Qcard ≤ 2 ^ (k + r * k + 1) := thresholdQuery_card_le_pow k r hrk
  have hQ2 : 2 ≤ Qcard := by
    dsimp [Qcard]
    rw [thresholdQuery_card]
    have hpow : 2 ≤ 2 ^ k := by
      change 2 ^ 1 ≤ 2 ^ k
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact hpow.trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    (boundedThresholdFamily k r).card ≤ (linearSignFamily thresholdVector).card :=
      Finset.card_mono (boundedThresholdFamily_subset_linear k r)
    _ ≤ 2 * Qcard ^ (k + 1) := linearSignFamily_card_le _ hQ2
    _ ≤ 2 * (2 ^ (k + r * k + 1)) ^ (k + 1) :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hQ _)
    _ = 2 ^ (1 + (k + r * k + 1) * (k + 1)) := by
      change 2 ^ 1 * (2 ^ (k + r * k + 1)) ^ (k + 1) = _
      rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (2 * r * k ^ 3) :=
      Nat.pow_le_pow_right (by decide) (finitePattern_exponent_bound k r hk hr)

/-! ### Corollary 17.5 -/

theorem corollary_17_5_holds : corollary_17_5 := by
  classical
  intro k r
  by_cases hk0 : k = 0
  · subst k
    refine ⟨{fun _ => 0}, by simp, ?_⟩
    intro alpha _
    simp only [Finset.mem_singleton]
    funext e
    simp [floorDotPattern]
  by_cases hr0 : r = 0
  · subst r
    refine ⟨∅, by simp, ?_⟩
    intro alpha ha
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hi := ha ⟨0, hkpos⟩
    simp only [Nat.cast_zero, neg_zero] at hi
    exact (lt_asymm hi.1 hi.2).elim
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  by_cases hk2 : 2 ≤ k
  · let F : Finset ((Fin k → Bool) → Int) :=
      (boundedThresholdFamily k r).attach.image fun u =>
        floorDotPattern (thresholdRepresentative k r u)
    refine ⟨F, ?_, ?_⟩
    · calc
        F.card ≤ (boundedThresholdFamily k r).attach.card := Finset.card_image_le
        _ = (boundedThresholdFamily k r).card := Finset.card_attach
        _ ≤ 2 ^ (2 * r * k ^ 3) :=
          boundedThresholdFamily_card_le k r hk2 hrpos
    · intro alpha ha
      have hu : thresholdPattern (R := r * k) alpha ∈ boundedThresholdFamily k r := by
        rw [boundedThresholdFamily, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, alpha, ha, rfl⟩
      let u : ↥(boundedThresholdFamily k r) :=
        ⟨thresholdPattern (R := r * k) alpha, hu⟩
      simp only [F, Finset.mem_image]
      refine ⟨u, Finset.mem_attach _ _, ?_⟩
      apply floorDotPattern_eq_of_thresholdPattern_eq hkpos hrpos
        (thresholdRepresentative k r u) alpha
        (thresholdRepresentative_bound k r u) ha
      simpa only [u] using thresholdRepresentative_pattern k r u
  · have hk1 : k = 1 := by omega
    subst k
    let I : Finset Int := Finset.Ico (-(r : Int)) (r : Int)
    let F : Finset ((Fin 1 → Bool) → Int) :=
      I.image fun z e => if e 0 then z else 0
    refine ⟨F, ?_, ?_⟩
    · have hI : I.card = 2 * r := by
        simp only [I]
        rw [Int.card_Ico, sub_neg_eq_add]
        rw [Int.toNat_add (by omega) (by omega)]
        omega
      calc
        F.card ≤ I.card := Finset.card_image_le
        _ = 2 * r := hI
        _ ≤ 2 ^ (2 * r) := Nat.lt_two_pow_self.le
        _ = 2 ^ (2 * r * 1 ^ 3) := by simp
    · intro alpha ha
      let z : Int := ⌊alpha 0⌋
      have hz : z ∈ I := by
        simp only [I, Finset.mem_Ico]
        constructor
        · apply Int.le_floor.mpr
          simpa [z] using (le_of_lt (ha 0).1)
        · apply Int.floor_lt.mpr
          simpa [z] using (ha 0).2
      simp only [F, Finset.mem_image]
      refine ⟨z, hz, ?_⟩
      funext e
      rw [floorDotPattern, Fin.sum_univ_one]
      cases e 0 <;> simp [z]

/-! ### Corollary 17.6 -/

private def fractionalAugment {k : Nat} (alpha0 : Real) (alpha : Fin k → Real) :
    Fin (k + 1) → Real :=
  Fin.cases (Int.fract alpha0) alpha

private lemma fractionalAugment_bound {k r : Nat} (hr : 0 < r)
    (alpha0 : Real) (alpha : Fin k → Real) (ha : coefficientBound r alpha) :
    coefficientBound r (fractionalAugment alpha0 alpha) := by
  intro i
  refine Fin.cases ?_ (fun j => ha j) i
  constructor
  · have hcast : (0 : Real) < r := by exact_mod_cast hr
    exact lt_of_lt_of_le (neg_neg_of_pos hcast) (Int.fract_nonneg alpha0)
  · exact (Int.fract_lt_one alpha0).trans_le (by exact_mod_cast hr)

private lemma floorDotPattern_fractionalAugment {k : Nat} (alpha0 : Real)
    (alpha : Fin k → Real) (e : Fin k → Bool) :
    floorDotPattern (fractionalAugment alpha0 alpha) (Fin.cases true e) =
      ⌊Int.fract alpha0 + subsetSum alpha e⌋ := by
  rw [floorDotPattern, Fin.sum_univ_succ]
  simp only [fractionalAugment, Fin.cases_zero, Fin.cases_succ, if_true, subsetSum]

private lemma floor_add_eq_floor_add_fract (a s : Real) :
    ⌊a + s⌋ = ⌊a⌋ + ⌊Int.fract a + s⌋ := by
  calc
    ⌊a + s⌋ = ⌊((⌊a⌋ : Int) : Real) + Int.fract a + s⌋ := by
      congr 1
      rw [Int.floor_add_fract]
    _ = ⌊a⌋ + ⌊Int.fract a + s⌋ := by
      rw [add_assoc, Int.floor_intCast_add]

theorem corollary_17_6_holds : corollary_17_6 := by
  classical
  intro k M r hM
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  by_cases hr0 : r = 0
  · subst r
    by_cases hk0 : k = 0
    · subst k
      refine ⟨Finset.univ, ?_, fun _ _ _ => Finset.mem_univ _⟩
      simp [ZMod.card]
    · refine ⟨∅, by simp, ?_⟩
      intro alpha0 alpha ha
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hi := ha ⟨0, hkpos⟩
      simp only [Nat.cast_zero, neg_zero] at hi
      exact (lt_asymm hi.1 hi.2).elim
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  obtain ⟨G, hGcard, hGmem⟩ := corollary_17_5_holds (k + 1) r
  let F : Finset ((Fin k → Bool) → ZMod M) :=
    (Finset.univ.product G).image fun p e =>
      p.1 + (p.2 (Fin.cases true e) : ZMod M)
  refine ⟨F, ?_, ?_⟩
  · calc
      F.card ≤ (Finset.univ.product G).card := Finset.card_image_le
      _ = M * G.card := by simp [ZMod.card]
      _ ≤ M * 2 ^ (2 * r * (k + 1) ^ 3) := Nat.mul_le_mul_left M hGcard
  · intro alpha0 alpha ha
    let beta := fractionalAugment alpha0 alpha
    have hbeta : coefficientBound r beta := fractionalAugment_bound hr alpha0 alpha ha
    have hG : floorDotPattern beta ∈ G := hGmem beta hbeta
    simp only [F, Finset.mem_image]
    refine ⟨(((⌊alpha0⌋ : Int) : ZMod M), floorDotPattern beta), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hG⟩
    · funext e
      change ((⌊alpha0⌋ : Int) : ZMod M) +
          ((floorDotPattern beta (Fin.cases true e) : Int) : ZMod M) =
        ((⌊alpha0 + subsetSum alpha e⌋ : Int) : ZMod M)
      rw [floorDotPattern_fractionalAugment]
      have hfloor := congrArg (fun z : Int => (z : ZMod M))
        (floor_add_eq_floor_add_fract alpha0 (subsetSum alpha e)).symm
      simpa only [Int.cast_add] using hfloor

end LeanProofs.GowersSzemeredi
