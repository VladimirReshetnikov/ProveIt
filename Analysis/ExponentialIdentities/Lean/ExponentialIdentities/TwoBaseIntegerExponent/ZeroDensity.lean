import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Additive.Corner.Roth

/-!
# Density bounds for two-base integral exponents

Write `α = log 3 / log 2`.  This file strengthens the consecutive-triple obstruction for the
sequence `m ↦ m ^ α` to arbitrary three-term arithmetic progressions.  Two applications of the
mean value theorem identify the second difference with

`α * (α - 1) * h ^ 2 * d ^ (α - 2)`

for an intermediate point `d`.  Since `1 < α < 8 / 5`, this lies strictly between zero and one
whenever `h ^ 5 ≤ n`.  Thus the corresponding three values cannot all be integers.

This curvature estimate is the analytic input for combining the candidate sequence with the
formalized Roth theorem in Mathlib.  The resulting theorem says that the number of positive
natural candidates below `N` is `o(N)`; a final corollary states this as convergence of their
proportion to zero.
-/

namespace LeanProofs.TwoBaseIntegerExponent

private theorem alpha_mul_sub_one_lt_one_ap :
    logThreeDivLogTwo * (logThreeDivLogTwo - 1) < 1 := by
  have hprod : 0 < ((8 / 5 : ℝ) - logThreeDivLogTwo) *
      (logThreeDivLogTwo + 3 / 5) :=
    mul_pos (sub_pos.mpr logThreeDivLogTwo_lt_eight_fifths)
      (by linarith [one_lt_logThreeDivLogTwo])
  nlinarith

/-- Exact second-difference mean-value identity at step `h`. -/
theorem exists_second_difference_point_ap (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) :
    ∃ d : ℝ, (n : ℝ) < d ∧ d < (n + 2 * h : ℕ) ∧
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo =
        logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (h : ℝ) ^ 2 * d ^ (logThreeDivLogTwo - 2) := by
  let α : ℝ := logThreeDivLogTwo
  let f : ℝ → ℝ := fun y ↦ y ^ α
  let g : ℝ → ℝ := fun y ↦ f (y + h) - f y
  let g' : ℝ → ℝ := fun y ↦ α * ((y + h) ^ (α - 1) - y ^ (α - 1))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hg_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt g (g' y) y := by
    have houter := Real.hasDerivAt_rpow_const (x := y + h) (p := α)
      (Or.inl (by positivity : y + (h : ℝ) ≠ 0))
    have hshift : HasDerivAt (fun z : ℝ ↦ (z + h) ^ α)
        (α * (y + h) ^ (α - 1)) y := by
      exact houter.comp_add_const y h
    have hbase := Real.hasDerivAt_rpow_const (x := y) (p := α) (Or.inl hy.ne')
    convert hshift.sub hbase using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
      | ring
  have hg_cont : ContinuousOn g (Set.Icc (n : ℝ) ((n : ℝ) + h)) := by
    intro y hy
    exact (hg_deriv y (hnpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope g g'
    (by linarith : (n : ℝ) < (n : ℝ) + h) hg_cont (by
      intro y hy
      exact hg_deriv y (hnpos.trans hy.1))
  have hcpos : 0 < c := hnpos.trans hc.1
  let q : ℝ → ℝ := fun y ↦ y ^ (α - 1)
  let q' : ℝ → ℝ := fun y ↦ (α - 1) * y ^ (α - 2)
  have hq_deriv (y : ℝ) (hy : 0 < y) : HasDerivAt q (q' y) y := by
    have hp := Real.hasDerivAt_rpow_const (x := y) (p := α - 1) (Or.inl hy.ne')
    change HasDerivAt (fun y : ℝ ↦ y ^ (α - 1)) ((α - 1) * y ^ (α - 2)) y
    rw [show α - 1 - 1 = α - 2 by ring] at hp
    exact hp
  have hq_cont : ContinuousOn q (Set.Icc c (c + h)) := by
    intro y hy
    exact (hq_deriv y (hcpos.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdEq⟩ := exists_hasDerivAt_eq_slope q q'
    (by linarith : c < c + h) hq_cont (by
      intro y hy
      exact hq_deriv y (hcpos.trans hy.1))
  refine ⟨d, hc.1.trans hd.1, ?_, ?_⟩
  · have hcup : c < (n : ℝ) + h := hc.2
    have hdup : d < c + h := hd.2
    push_cast
    linarith
  · have hhne : (h : ℝ) ≠ 0 := ne_of_gt hhpos
    have hcEq' : g ((n : ℝ) + h) - g n = g' c * h := by
      exact ((eq_div_iff hhne).mp (by simpa using hcEq)).symm
    have hdEq' : q (c + h) - q c = q' d * h := by
      exact ((eq_div_iff hhne).mp (by simpa using hdEq)).symm
    dsimp only [g', q'] at hcEq' hdEq'
    dsimp only [g, f, q, α] at hcEq' hdEq' ⊢
    rw [hdEq'] at hcEq'
    push_cast at hcEq' ⊢
    ring_nf at hcEq' ⊢
    exact hcEq'

/-- A strict curvature bound for the second difference at an arbitrary positive step. -/
theorem second_difference_logThreeDivLogTwo_ap_bound
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) :
    0 < ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo ∧
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo <
        logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) := by
  obtain ⟨d, hdlo, _hdhi, hdEq⟩ := exists_second_difference_point_ap n h hn hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hα0 : 0 < logThreeDivLogTwo := lt_trans zero_lt_one one_lt_logThreeDivLogTwo
  have hα1 : 0 < logThreeDivLogTwo - 1 := sub_pos.mpr one_lt_logThreeDivLogTwo
  have hαtwo : logThreeDivLogTwo - 2 < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hdpow0 : 0 < d ^ (logThreeDivLogTwo - 2) :=
    Real.rpow_pos_of_pos (hnpos.trans hdlo) _
  have hpowlt : d ^ (logThreeDivLogTwo - 2) <
      (n : ℝ) ^ (logThreeDivLogTwo - 2) :=
    Real.rpow_lt_rpow_of_neg hnpos hdlo hαtwo
  constructor
  · rw [hdEq]
    positivity
  · rw [hdEq]
    gcongr

/-- If `h ^ 5 ≤ n`, the step-`h` second difference lies strictly between zero and one. -/
theorem second_difference_logThreeDivLogTwo_ap
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hscale : h ^ 5 ≤ n) :
    0 < ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo ∧
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo < 1 := by
  obtain ⟨hpos, hbound⟩ := second_difference_logThreeDivLogTwo_ap_bound n h hn hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hh_one : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hαtwo : logThreeDivLogTwo - 2 < 0 := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hscaleR : ((h : ℝ) ^ 5) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow5pos : 0 < (h : ℝ) ^ 5 := pow_pos hhpos _
  have hn_rpow_le : (n : ℝ) ^ (logThreeDivLogTwo - 2) ≤
      ((h : ℝ) ^ 5) ^ (logThreeDivLogTwo - 2) :=
    (Real.rpow_le_rpow_iff_of_neg hnpos hpow5pos hαtwo).2 hscaleR
  have hpow5_rpow : ((h : ℝ) ^ 5) ^ (logThreeDivLogTwo - 2) =
      (h : ℝ) ^ (5 * (logThreeDivLogTwo - 2)) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul hhpos.le 5 (logThreeDivLogTwo - 2)).symm
  have hexp : 5 * (logThreeDivLogTwo - 2) ≤ (-2 : ℝ) := by
    linarith [logThreeDivLogTwo_lt_eight_fifths]
  have hpow_exp_le :
      (h : ℝ) ^ (5 * (logThreeDivLogTwo - 2)) ≤ (h : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hh_one hexp
  have hsize : (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) ≤ 1 := by
    calc
      (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) ≤
          (h : ℝ) ^ 2 * ((h : ℝ) ^ 5) ^ (logThreeDivLogTwo - 2) := by
        gcongr
      _ = (h : ℝ) ^ 2 * (h : ℝ) ^ (5 * (logThreeDivLogTwo - 2)) := by
        rw [hpow5_rpow]
      _ ≤ (h : ℝ) ^ 2 * (h : ℝ) ^ (-2 : ℝ) := by
        gcongr
      _ = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hhpos]
        norm_num
  have hsizepos : 0 < (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) := by
    positivity
  have hcoeflt :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          ((h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2)) <
        (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) := by
    simpa using mul_lt_mul_of_pos_right alpha_mul_sub_one_lt_one_ap hsizepos
  constructor
  · exact hpos
  · calc
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
            2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
            (n : ℝ) ^ logThreeDivLogTwo <
          logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
            (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) := hbound
      _ = logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
          ((h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2)) := by ring
      _ < (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) := hcoeflt
      _ ≤ 1 := hsize

/-- Three integral candidate values cannot occur in an arithmetic progression of step `h` once
`h ^ 5 ≤ n`. -/
theorem not_three_arithmetic_progression_logThreeDivLogTwo_rpow_integers
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hscale : h ^ 5 ≤ n)
    (h₀ : ∃ z : ℤ, (z : ℝ) = (n : ℝ) ^ logThreeDivLogTwo)
    (h₁ : ∃ z : ℤ, (z : ℝ) = ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo)
    (h₂ : ∃ z : ℤ, (z : ℝ) = ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo) :
    False := by
  obtain ⟨z₀, hz₀⟩ := h₀
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨hpos, hlt⟩ := second_difference_logThreeDivLogTwo_ap n h hn hh hscale
  have hzpos : (0 : ℤ) < z₂ - 2 * z₁ + z₀ := by
    exact_mod_cast (show (0 : ℝ) <
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) by
        rw [hz₂, hz₁, hz₀]
        exact hpos)
  have hzlt : z₂ - 2 * z₁ + z₀ < (1 : ℤ) := by
    exact_mod_cast (show
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) < 1 by
        rw [hz₂, hz₁, hz₀]
        exact hlt)
  omega

/-- Arithmetic-progression obstruction stated directly for natural candidates. -/
theorem not_three_arithmetic_progression_twoBaseNaturalCandidates
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hscale : h ^ 5 ≤ n) :
    ¬(TwoBaseNaturalCandidate n ∧
      TwoBaseNaturalCandidate (n + h) ∧
      TwoBaseNaturalCandidate (n + 2 * h)) := by
  rintro ⟨h₀, h₁, h₂⟩
  exact not_three_arithmetic_progression_logThreeDivLogTwo_rpow_integers
    n h hn hh hscale h₀.2 h₁.2 h₂.2

open Set Finset Asymptotics Filter

namespace CandidateDensity

variable (C : ℕ → Prop) [DecidablePred C]

/-- An obstruction to three candidates in an arithmetic progression once the first term
dominates the fifth power of the step. -/
def APObstruction : Prop :=
  ∀ n h : ℕ, 1 ≤ h → h ^ 5 ≤ n → C n → C (n + h) → C (n + 2 * h) → False

/-- Candidate offsets in a length-`H` block beginning at `start`. -/
def blockOffsets (start H : ℕ) : Finset ℕ :=
  (range H).filter fun j ↦ C (start + j)

theorem blockOffsets_subset_range (start H : ℕ) : blockOffsets C start H ⊆ range H :=
  filter_subset _ _

/-- Every block of length `H` beginning at or beyond `H ^ 5` is 3AP-free. -/
theorem blockOffsets_threeAPFree (hC : APObstruction C)
    {start H : ℕ} (hstart : H ^ 5 ≤ start) :
    ThreeAPFree (blockOffsets C start H : Set ℕ) := by
  rw [ThreeAPFree]
  intro a ha b hb c hc hac
  by_contra hab
  have ha' := mem_filter.mp ha
  have hb' := mem_filter.mp hb
  have hc' := mem_filter.mp hc
  have haH : a < H := mem_range.mp ha'.1
  have hbH : b < H := mem_range.mp hb'.1
  have hcH : c < H := mem_range.mp hc'.1
  rcases lt_or_gt_of_ne hab with hablt | habgt
  · let h := b - a
    have hh : 1 ≤ h := by dsimp [h]; omega
    have hhH : h ≤ H := by dsimp [h]; omega
    have hh5H : h ^ 5 ≤ H ^ 5 := Nat.pow_le_pow_left hhH 5
    have hh5n : h ^ 5 ≤ start + a := hh5H.trans (hstart.trans (Nat.le_add_right _ _))
    apply hC (start + a) h hh hh5n ha'.2
    · have heq : start + a + h = start + b := by dsimp [h]; omega
      simpa only [heq] using hb'.2
    · have heq : start + a + 2 * h = start + c := by dsimp [h]; omega
      simpa only [heq] using hc'.2
  · have hcb : c < b := by omega
    let h := b - c
    have hh : 1 ≤ h := by dsimp [h]; omega
    have hhH : h ≤ H := by dsimp [h]; omega
    have hh5H : h ^ 5 ≤ H ^ 5 := Nat.pow_le_pow_left hhH 5
    have hh5n : h ^ 5 ≤ start + c := hh5H.trans (hstart.trans (Nat.le_add_right _ _))
    apply hC (start + c) h hh hh5n hc'.2
    · have heq : start + c + h = start + b := by dsimp [h]; omega
      simpa only [heq] using hb'.2
    · have heq : start + c + 2 * h = start + a := by dsimp [h]; omega
      simpa only [heq] using ha'.2

/-- Roth-number upper bound for every sufficiently far block. -/
theorem blockOffsets_card_le_rothNumberNat (hC : APObstruction C)
    {start H : ℕ} (hstart : H ^ 5 ≤ start) :
    (blockOffsets C start H).card ≤ rothNumberNat H := by
  exact ThreeAPFree.le_rothNumberNat _
    (blockOffsets_threeAPFree C hC hstart)
    (fun x hx ↦ mem_range.mp ((mem_filter.mp hx).1)) rfl

/-- Candidates below `N`. -/
def candidatesBelow (N : ℕ) : Finset ℕ := (range N).filter C

/-- The block of actual candidate values corresponding to `blockOffsets`. -/
def blockValues (start H : ℕ) : Finset ℕ :=
  (blockOffsets C start H).image fun j ↦ start + j

theorem card_blockValues (start H : ℕ) :
    (blockValues C start H).card = (blockOffsets C start H).card := by
  exact card_image_of_injective _ fun _ _ h ↦ Nat.add_left_cancel h

theorem mem_blockValues_iff {start H m : ℕ} :
    m ∈ blockValues C start H ↔ start ≤ m ∧ m < start + H ∧ C m := by
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hj' := mem_filter.mp hj
    have hjH : j < H := mem_range.mp hj'.1
    exact ⟨by omega, by omega, hj'.2⟩
  · rintro ⟨hsm, hmH, hmC⟩
    apply mem_image.mpr
    refine ⟨m - start, ?_, by omega⟩
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by omega), by simpa [Nat.add_sub_of_le hsm] using hmC⟩

/-- A finite cover of the candidates below `N`: the initial segment of length `H ^ 5`, followed
by aligned blocks of length `H`; the final block may extend past `N`. -/
theorem candidatesBelow_subset_initial_union_blocks (N H : ℕ) (hH : 1 ≤ H) :
    candidatesBelow C N ⊆
      range (H ^ 5) ∪
        (range ((N - H ^ 5) ⌈/⌉ H)).biUnion
          (fun k ↦ blockValues C (H ^ 5 + k * H) H) := by
  intro m hm
  have hm' := mem_filter.mp hm
  have hmN : m < N := mem_range.mp hm'.1
  by_cases hm0 : m < H ^ 5
  · exact mem_union_left _ (mem_range.mpr hm0)
  · apply Finset.mem_union_right
    apply mem_biUnion.mpr
    let k := (m - H ^ 5) / H
    have hHpos : 0 < H := by omega
    have hsub_lt : m - H ^ 5 < N - H ^ 5 :=
      Nat.sub_lt_sub_right (Nat.le_of_not_gt hm0) hmN
    have hmul_le : H * k ≤ m - H ^ 5 := by
      dsimp [k]
      exact Nat.mul_div_le _ _
    have hceil : N - H ^ 5 ≤ H * ((N - H ^ 5) ⌈/⌉ H) := by
      have hx := le_smul_ceilDiv (a := H) (b := N - H ^ 5) hHpos
      change N - H ^ 5 ≤ H * ((N - H ^ 5) ⌈/⌉ H) at hx
      exact hx
    have hmul_lt : H * k < H * ((N - H ^ 5) ⌈/⌉ H) :=
      hmul_le.trans_lt (hsub_lt.trans_le hceil)
    have hk : k < (N - H ^ 5) ⌈/⌉ H :=
      (Nat.mul_lt_mul_left hHpos).mp hmul_lt
    refine ⟨k, mem_range.mpr hk, ?_⟩
    apply mem_blockValues_iff (C := C) |>.mpr
    dsimp [k]
    have hmstart : H ^ 5 ≤ m := Nat.le_of_not_gt hm0
    constructor
    · calc
        H ^ 5 + (m - H ^ 5) / H * H ≤ H ^ 5 + (m - H ^ 5) :=
          Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
        _ = m := Nat.add_sub_of_le hmstart
    constructor
    · have hmod := Nat.mod_lt (m - H ^ 5) (by omega : 0 < H)
      have hreconstruct :
          (m - H ^ 5) / H * H + (m - H ^ 5) % H = m - H ^ 5 := by
        simpa [mul_comm] using Nat.div_add_mod (m - H ^ 5) H
      calc
        m = H ^ 5 + (m - H ^ 5) := (Nat.add_sub_of_le hmstart).symm
        _ = H ^ 5 + ((m - H ^ 5) / H * H + (m - H ^ 5) % H) := by
          rw [hreconstruct]
        _ < H ^ 5 + ((m - H ^ 5) / H * H + H) := by omega
        _ = H ^ 5 + (m - H ^ 5) / H * H + H := by omega
    · exact hm'.2

/-- Quantitative block-cover bound. -/
theorem candidatesBelow_card_le (hC : APObstruction C)
    (N H : ℕ) (hH : 1 ≤ H) :
    (candidatesBelow C N).card ≤
      H ^ 5 + ((N - H ^ 5) ⌈/⌉ H) * rothNumberNat H := by
  let K := (N - H ^ 5) ⌈/⌉ H
  let blocks := (range K).biUnion (fun k ↦ blockValues C (H ^ 5 + k * H) H)
  have hsub : candidatesBelow C N ⊆ range (H ^ 5) ∪ blocks := by
    simpa only [K, blocks] using candidatesBelow_subset_initial_union_blocks C N H hH
  calc
    (candidatesBelow C N).card ≤ (range (H ^ 5) ∪ blocks).card := card_le_card hsub
    _ ≤ (range (H ^ 5)).card + blocks.card := card_union_le _ _
    _ ≤ H ^ 5 + ∑ k ∈ range K, (blockValues C (H ^ 5 + k * H) H).card := by
      simp only [card_range, add_le_add_iff_left]
      exact card_biUnion_le
    _ = H ^ 5 + ∑ k ∈ range K, (blockOffsets C (H ^ 5 + k * H) H).card := by
      congr 1
      apply sum_congr rfl
      intro k _
      exact card_blockValues C _ _
    _ ≤ H ^ 5 + ∑ _k ∈ range K, rothNumberNat H := by
      gcongr with k hk
      apply blockOffsets_card_le_rothNumberNat C hC
      exact Nat.le_add_right _ _
    _ = H ^ 5 + K * rothNumberNat H := by simp
    _ = H ^ 5 + ((N - H ^ 5) ⌈/⌉ H) * rothNumberNat H := rfl

/-- An eventual arithmetic-progression obstruction, combined with Mathlib's formal Roth theorem,
forces the candidate set to have natural density zero. -/
theorem candidatesBelow_isLittleO_id (hC : APObstruction C) :
    (fun N ↦ ((candidatesBelow C N).card : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  have hroth := (isLittleO_iff.mp rothNumberNat_isLittleO_id) hδ
  rw [eventually_atTop] at hroth
  obtain ⟨H₀, hH₀⟩ := hroth
  let H := max H₀ 1
  have hH : 1 ≤ H := le_max_right _ _
  have hHpos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hRHnorm := hH₀ H (le_max_left _ _)
  have hRH : (rothNumberNat H : ℝ) ≤ (ε / 4) * (H : ℝ) := by
    simpa only [Real.norm_natCast] using hRHnorm
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (2 * ((H ^ 5 : ℕ) : ℝ) / ε)
  refine eventually_atTop.mpr ⟨max H M₀, ?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hM₀N : M₀ ≤ N := (le_max_right _ _).trans hN
  have hinitial : ((H ^ 5 : ℕ) : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hM₀N' : (M₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hM₀N
    have htwo : 2 * ((H ^ 5 : ℕ) : ℝ) < ε * (M₀ : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hM₀
    nlinarith
  let K := (N - H ^ 5) ⌈/⌉ H
  have hKH : K * H ≤ N + H := by
    dsimp only [K]
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc
      (N - H ^ 5 + H - 1) / H * H ≤ N - H ^ 5 + H - 1 :=
        Nat.div_mul_le_self _ _
      _ ≤ N + H := by omega
  have hcount := candidatesBelow_card_le C hC N H hH
  have hcount' : ((candidatesBelow C N).card : ℝ) ≤
      ((H ^ 5 : ℕ) : ℝ) + (K : ℝ) * (rothNumberNat H : ℝ) := by
    exact_mod_cast hcount
  have hKH' : (K : ℝ) * (H : ℝ) ≤ (N : ℝ) + (H : ℝ) := by
    exact_mod_cast hKH
  have hHN' : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hHN
  simp only [Real.norm_natCast]
  calc
    ((candidatesBelow C N).card : ℝ) ≤
        ((H ^ 5 : ℕ) : ℝ) + (K : ℝ) * (rothNumberNat H : ℝ) := hcount'
    _ ≤ ((H ^ 5 : ℕ) : ℝ) + (K : ℝ) * ((ε / 4) * (H : ℝ)) := by
      gcongr
    _ = ((H ^ 5 : ℕ) : ℝ) + (ε / 4) * ((K : ℝ) * (H : ℝ)) := by ring
    _ ≤ ((H ^ 5 : ℕ) : ℝ) + (ε / 4) * ((N : ℝ) + (H : ℝ)) := by
      gcongr
    _ ≤ (ε / 2) * (N : ℝ) + (ε / 4) * (2 * (N : ℝ)) := by
      gcongr
      linarith
    _ = ε * (N : ℝ) := by ring

end CandidateDensity

/-- Positive natural two-base candidates below `N`. (`0` is filtered out by the candidate
predicate itself.) -/
noncomputable def twoBaseNaturalCandidatesBelow (N : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter TwoBaseNaturalCandidate

private theorem twoBaseNaturalCandidate_ap_obstruction :
    CandidateDensity.APObstruction TwoBaseNaturalCandidate := by
  intro n h hh hscale hn hn1 hn2
  have hnpos : 1 ≤ n := (one_le_pow₀ hh).trans hscale
  exact not_three_arithmetic_progression_twoBaseNaturalCandidates
    n h hnpos hh hscale ⟨hn, hn1, hn2⟩

/-- A finite quantitative form of the density bound.  For every block length `H ≥ 1`, the
number of natural two-base candidates below `N` is bounded by an initial exceptional segment of
length `H ^ 5` plus one Roth-number contribution for each remaining block. -/
theorem twoBaseNaturalCandidatesBelow_card_le (N H : ℕ) (hH : 1 ≤ H) :
    (twoBaseNaturalCandidatesBelow N).card ≤
      H ^ 5 + ((N - H ^ 5) ⌈/⌉ H) * rothNumberNat H := by
  classical
  simpa only [twoBaseNaturalCandidatesBelow, CandidateDensity.candidatesBelow] using
    CandidateDensity.candidatesBelow_card_le TwoBaseNaturalCandidate
      twoBaseNaturalCandidate_ap_obstruction N H hH

/-- The number of natural values `m < N` for which both the associated powers of two and three
are integral is `o(N)`. Equivalently, the natural candidates have asymptotic density zero. -/
theorem twoBaseNaturalCandidatesBelow_isLittleO_id :
    (fun N ↦ ((twoBaseNaturalCandidatesBelow N).card : ℝ)) =o[atTop]
      (fun N ↦ (N : ℝ)) := by
  classical
  simpa only [twoBaseNaturalCandidatesBelow, CandidateDensity.candidatesBelow] using
    CandidateDensity.candidatesBelow_isLittleO_id TwoBaseNaturalCandidate
      twoBaseNaturalCandidate_ap_obstruction

/-- Ratio form of the zero-density theorem for positive natural two-base candidates. -/
theorem tendsto_twoBaseNaturalCandidatesBelow_density_zero :
    Tendsto
      (fun N ↦ ((twoBaseNaturalCandidatesBelow N).card : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
  twoBaseNaturalCandidatesBelow_isLittleO_id.tendsto_div_nhds_zero

end LeanProofs.TwoBaseIntegerExponent
