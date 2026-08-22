import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Exact probability laws for mechanical Sturmian carries

For a slope `α ∈ [0,1)`, the increment of the floor under translation by `α` is the
indicator of a terminal circular interval.  This file proves the exact telescoping law for
finite prefixes, their two-value distribution, mean and variance under uniform initial phase,
the bounded-coboundary identity, and the circular interval-intersection formula giving the
two-point covariance kernel.
-/

open scoped BigOperators
open MeasureTheory Set

namespace LeanProofs.TwoBaseIntegerExponent

/-- The carry made when the fractional part of `x` is incremented by `α`. -/
noncomputable def carryBit (α x : ℝ) : ℤ :=
  if 1 - α ≤ Int.fract x then 1 else 0

/-- For an increment in `[0,1)`, the floor increment is exactly the circular carry bit. -/
theorem floor_add_sub_floor_eq_carryBit {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (x : ℝ) :
    ⌊x + α⌋ - ⌊x⌋ = carryBit α x := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := by
    simpa only [add_comm] using (Int.floor_add_fract x).symm
  have hfloor : ⌊x + α⌋ = ⌊x⌋ + ⌊Int.fract x + α⌋ := by
    calc
      ⌊x + α⌋ = ⌊(⌊x⌋ : ℝ) + (Int.fract x + α)⌋ := by
        congr 1
        calc
          x + α = ((⌊x⌋ : ℝ) + Int.fract x) + α :=
            congrArg (fun y : ℝ => y + α) hx
          _ = (⌊x⌋ : ℝ) + (Int.fract x + α) := by ring
      _ = ⌊x⌋ + ⌊Int.fract x + α⌋ :=
        Int.floor_intCast_add (⌊x⌋ : ℤ) (Int.fract x + α)
  rw [hfloor, carryBit]
  by_cases hcarry : 1 - α ≤ Int.fract x
  · rw [if_pos hcarry]
    have hlo : (1 : ℝ) ≤ Int.fract x + α := by linarith
    have hhi : Int.fract x + α < (1 : ℝ) + 1 := by
      linarith [Int.fract_lt_one x]
    have : ⌊Int.fract x + α⌋ = (1 : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast hlo, by norm_num at hhi ⊢; exact hhi⟩
    omega
  · rw [if_neg hcarry]
    have hlo : (0 : ℝ) ≤ Int.fract x + α :=
      add_nonneg (Int.fract_nonneg x) hα0
    have hhi : Int.fract x + α < 1 := by linarith
    have : ⌊Int.fract x + α⌋ = (0 : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast hlo, by norm_num at hhi ⊢; exact hhi⟩
    omega

/-- The `j`th mechanical-word bit with phase `t` and slope `α`. -/
noncomputable def bit (α t : ℝ) (j : ℕ) : ℤ := carryBit α (t + j * α)

theorem bit_eq_floor_difference {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (t : ℝ) (j : ℕ) :
    bit α t j = ⌊t + (j + 1) * α⌋ - ⌊t + j * α⌋ := by
  rw [bit]
  symm
  convert floor_add_sub_floor_eq_carryBit hα0 hα1 (t + j * α) using 1 <;>
    norm_num [Nat.cast_add, Nat.cast_one] <;> ring

/-- Exact telescoping law for every finite Sturmian prefix. -/
theorem sum_bit_eq_floor_difference {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (t : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, bit α t j = ⌊t + N * α⌋ - ⌊t⌋ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, bit_eq_floor_difference hα0 hα1]
      norm_num [Nat.cast_add, Nat.cast_one]

/-- On the standard representative interval, the exact prefix is a base floor plus one
additional carry.  This is the deterministic core of the two-point distribution. -/
theorem sum_bit_eq_floor_add_carry {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, bit α t j =
      ⌊(N : ℝ) * α⌋ + (if 1 - Int.fract ((N : ℝ) * α) ≤ t then 1 else 0) := by
  rw [sum_bit_eq_floor_difference hα0 hα1]
  have hft : ⌊t⌋ = (0 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by exact_mod_cast ht0, by norm_num at ht1 ⊢; exact ht1⟩
  rw [hft, sub_zero]
  have hfract0 : 0 ≤ Int.fract ((N : ℝ) * α) := Int.fract_nonneg _
  have hfract1 : Int.fract ((N : ℝ) * α) < 1 := Int.fract_lt_one _
  have hdecomp :
      t + (N : ℝ) * α =
        (⌊(N : ℝ) * α⌋ : ℝ) + (t + Int.fract ((N : ℝ) * α)) := by
    linarith [Int.floor_add_fract ((N : ℝ) * α)]
  rw [hdecomp, Int.floor_intCast_add]
  have hcarry := floor_add_sub_floor_eq_carryBit hfract0 hfract1 t
  rw [carryBit, Int.fract_eq_self.mpr ⟨ht0, ht1⟩] at hcarry
  omega

/-- Consequently every prefix count has one of two consecutive values. -/
theorem sum_bit_two_values {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, bit α t j = ⌊(N : ℝ) * α⌋ ∨
      ∑ j ∈ Finset.range N, bit α t j = ⌊(N : ℝ) * α⌋ + 1 := by
  rw [sum_bit_eq_floor_add_carry hα0 hα1 ht0 ht1]
  split_ifs <;> simp

/-- Centering a carry gives the standard bounded coboundary. -/
theorem carryBit_sub_eq_coboundary {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (carryBit α t : ℝ) - α = t - Int.fract (t + α) := by
  have hcarry := floor_add_sub_floor_eq_carryBit hα0 hα1 t
  have hft : ⌊t⌋ = (0 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by exact_mod_cast ht0, by norm_num at ht1 ⊢; exact ht1⟩
  have hdecomp : (⌊t + α⌋ : ℝ) + Int.fract (t + α) = t + α :=
    Int.floor_add_fract (t + α)
  rw [hft, sub_zero] at hcarry
  have hcarryR : (⌊t + α⌋ : ℝ) = (carryBit α t : ℝ) := by
    exact_mod_cast hcarry
  linarith

private theorem integral_const_unit (c : ℝ) :
    ∫ _t in Ico (0 : ℝ) 1, c = c := by
  rw [integral_const]
  simp [measureReal_def, Real.volume_Ico]

/-- The real-valued prefix count. -/
noncomputable def prefixCount (α t : ℝ) (N : ℕ) : ℝ :=
  ((∑ j ∈ Finset.range N, bit α t j : ℤ) : ℝ)

/-- Pointwise Bernoulli decomposition of the prefix count on the standard representative
interval. -/
theorem prefixCount_eq_floor_add_indicator {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ht : t ∈ Ico (0 : ℝ) 1) (N : ℕ) :
    prefixCount α t N = (⌊(N : ℝ) * α⌋ : ℝ) +
      (Ico (1 - Int.fract ((N : ℝ) * α)) 1).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  have hsum := sum_bit_eq_floor_add_carry hα0 hα1 ht.1 ht.2 N
  rw [prefixCount, hsum]
  by_cases hcarry : 1 - Int.fract ((N : ℝ) * α) ≤ t
  · simp [hcarry, ht.2]
  · simp [hcarry]

private theorem integral_indicator_Ico_const {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in Ico (0 : ℝ) 1,
      (Ico (1 - r) 1).indicator (fun _ : ℝ => c) t = r * c := by
  rw [integral_indicator_const c measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (1 - r) 1 ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  rw [inter_eq_left.mpr hsub]
  simp [measureReal_def, Real.volume_Ico, hr0]

private theorem integral_indicator_Ico {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in Ico (0 : ℝ) 1,
      (Ico (1 - r) 1).indicator (fun _ : ℝ => (1 : ℝ)) t = r := by
  simpa using integral_indicator_Ico_const (c := (1 : ℝ)) hr0 hr1

/-- Exact mean of a length-`N` Sturmian prefix under uniform initial phase. -/
theorem prefixCount_mean {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (N : ℕ) :
    ∫ t in Ico (0 : ℝ) 1, prefixCount α t N = (N : ℝ) * α := by
  let r := Int.fract ((N : ℝ) * α)
  let m : ℝ := (⌊(N : ℝ) * α⌋ : ℝ)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ico
    (fun t ht => prefixCount_eq_floor_add_indicator hα0 hα1 ht N)]
  have hconst : Integrable (fun _ : ℝ => m) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrable_const_iff.mpr (Or.inr inferInstance)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrable_const_iff.mpr (Or.inr inferInstance)
  have hind : Integrable
      ((Ico (1 - r) 1).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 1)) := hone.indicator measurableSet_Ico
  change ∫ t in Ico (0 : ℝ) 1,
      m + (Ico (1 - r) 1).indicator (fun _ : ℝ => (1 : ℝ)) t = _
  rw [integral_add hconst hind, integral_const_unit]
  rw [show (∫ t in Ico (0 : ℝ) 1,
      (Ico (1 - r) 1).indicator (fun _ : ℝ => (1 : ℝ)) t) = r by
    exact integral_indicator_Ico (Int.fract_nonneg _) (Int.fract_lt_one _)]
  dsimp [m, r]
  linarith [Int.floor_add_fract ((N : ℝ) * α)]

/-- Exact variance of a length-`N` prefix.  The square-integral is taken against the
probability measure given by Lebesgue measure on `[0,1)`. -/
theorem prefixCount_variance {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (N : ℕ) :
    ∫ t in Ico (0 : ℝ) 1, (prefixCount α t N - (N : ℝ) * α) ^ 2 =
      Int.fract ((N : ℝ) * α) * (1 - Int.fract ((N : ℝ) * α)) := by
  let r := Int.fract ((N : ℝ) * α)
  let m : ℝ := (⌊(N : ℝ) * α⌋ : ℝ)
  let A := Ico (1 - r) 1
  have hr0 : 0 ≤ r := Int.fract_nonneg _
  have hr1 : r < 1 := Int.fract_lt_one _
  have hy : (N : ℝ) * α = m + r := by
    dsimp [m, r]
    exact (Int.floor_add_fract ((N : ℝ) * α)).symm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ico (fun t ht => ?_)]
  · have hconst : Integrable (fun _ : ℝ => r ^ 2)
        (volume.restrict (Ico (0 : ℝ) 1)) :=
      integrable_const_iff.mpr (Or.inr inferInstance)
    have hone : Integrable (fun _ : ℝ => (1 - 2 * r))
        (volume.restrict (Ico (0 : ℝ) 1)) :=
      integrable_const_iff.mpr (Or.inr inferInstance)
    have hind : Integrable (A.indicator (fun _ : ℝ => (1 - 2 * r)))
        (volume.restrict (Ico (0 : ℝ) 1)) := hone.indicator measurableSet_Ico
    change ∫ t in Ico (0 : ℝ) 1,
        r ^ 2 + A.indicator (fun _ : ℝ => (1 - 2 * r)) t = _
    rw [integral_add hconst hind, integral_const_unit]
    rw [show (∫ t in Ico (0 : ℝ) 1,
        A.indicator (fun _ : ℝ => (1 - 2 * r)) t) = r * (1 - 2 * r) by
      exact integral_indicator_Ico_const hr0 hr1]
    dsimp [r]
    ring
  · have hp := prefixCount_eq_floor_add_indicator hα0 hα1 ht N
    have hp' : prefixCount α t N = m + A.indicator (fun _ : ℝ => (1 : ℝ)) t := by
      simpa only [m, r, A] using hp
    change (prefixCount α t N - (N : ℝ) * α) ^ 2 =
      r ^ 2 + A.indicator (fun _ : ℝ => (1 - 2 * r)) t
    rw [hp', hy]
    by_cases hA : t ∈ A <;> simp [A, hA] <;> ring

/-- On `[0,1)`, a carry occurs precisely in the terminal interval of length `α`. -/
theorem carryBit_eq_one_iff {α t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    carryBit α t = 1 ↔ 1 - α ≤ t := by
  rw [carryBit, Int.fract_eq_self.mpr ⟨ht0, ht1⟩]
  by_cases h : 1 - α ≤ t <;> simp [h]

private theorem fract_add_eq_self {t δ : ℝ} (ht0 : 0 ≤ t) (hδ0 : 0 ≤ δ)
    (h : t + δ < 1) : Int.fract (t + δ) = t + δ :=
  Int.fract_eq_self.mpr ⟨add_nonneg ht0 hδ0, h⟩

private theorem fract_add_eq_sub_one {t δ : ℝ} (h : 1 ≤ t + δ)
    (ht1 : t < 1) (hδ1 : δ < 1) :
    Int.fract (t + δ) = t + δ - 1 := by
  calc
    Int.fract (t + δ) = Int.fract ((t + δ) - (1 : ℤ)) := by
      symm
      exact Int.fract_sub_intCast (t + δ) 1
    _ = t + δ - 1 := by
      have hb : Int.fract (t + δ - (1 : ℝ)) = t + δ - (1 : ℝ) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      norm_num at hb ⊢
      exact hb

/-- The event that two carries, separated by the circular displacement `δ`, both occur. -/
def jointCarrySet (α δ : ℝ) : Set ℝ :=
  {t | t ∈ Ico (0 : ℝ) 1 ∧ carryBit α t = 1 ∧ carryBit α (t + δ) = 1}

/-- Exact interval decomposition of the joint-carry event. -/
theorem jointCarrySet_eq_union {α δ : ℝ} (_hα0 : 0 ≤ α) (hα1 : α < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    jointCarrySet α δ = Ico (1 - α) (1 - δ) ∪ Ico (2 - α - δ) 1 := by
  ext t
  constructor
  · rintro ⟨ht, hfirst, hsecond⟩
    have hfirst' : 1 - α ≤ t := (carryBit_eq_one_iff ht.1 ht.2).mp hfirst
    by_cases hwrap : t + δ < 1
    · left
      exact ⟨hfirst', by linarith⟩
    · right
      have hfract : Int.fract (t + δ) = t + δ - 1 :=
        fract_add_eq_sub_one (le_of_not_gt hwrap) ht.2 hδ1
      have hthreshold : 1 - α ≤ Int.fract (t + δ) := by
        by_contra hn
        simp [carryBit, hn] at hsecond
      rw [hfract] at hthreshold
      exact ⟨by linarith, ht.2⟩
  · rintro (hleft | hright)
    · have ht0 : 0 ≤ t := by linarith [hleft.1, hα1]
      have ht1 : t < 1 := by linarith [hleft.2, hδ0]
      have hwrap : t + δ < 1 := by linarith [hleft.2]
      have hfract : Int.fract (t + δ) = t + δ :=
        fract_add_eq_self ht0 hδ0 hwrap
      refine ⟨⟨ht0, ht1⟩, (carryBit_eq_one_iff ht0 ht1).mpr hleft.1, ?_⟩
      rw [carryBit, hfract, if_pos]
      linarith [hleft.1]
    · have ht0 : 0 ≤ t := by linarith [hright.1, hα1, hδ1]
      have ht1 : t < 1 := hright.2
      have hfirst : 1 - α ≤ t := by linarith [hright.1, hδ1]
      have hwrap : 1 ≤ t + δ := by linarith [hright.1, hα1]
      have hfract : Int.fract (t + δ) = t + δ - 1 :=
        fract_add_eq_sub_one hwrap ht1 hδ1
      refine ⟨⟨ht0, ht1⟩, (carryBit_eq_one_iff ht0 ht1).mpr hfirst, ?_⟩
      rw [carryBit, hfract, if_pos]
      linarith [hright.1]

/-- The joint-carry probability is the sum of the two circular overlap lengths. -/
theorem jointCarrySet_measureReal {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    volume.real (jointCarrySet α δ) =
      max 0 (α - δ) + max 0 (α + δ - 1) := by
  rw [jointCarrySet_eq_union hα0 hα1 hδ0 hδ1]
  have hd : Disjoint (Ico (1 - α) (1 - δ)) (Ico (2 - α - δ) 1) := by
    rw [Set.disjoint_left]
    intro t hleft hright
    linarith [hleft.2, hright.1, hα1]
  rw [measureReal_def, measure_union hd measurableSet_Ico]
  rw [ENNReal.toReal_add (by simp [Real.volume_Ico]) (by simp [Real.volume_Ico])]
  simp only [Real.volume_Ico]
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  ring_nf
  simp only [max_comm]

/-- Integral form of the circular interval-intersection formula. -/
theorem jointCarry_integral {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∫ t in Ico (0 : ℝ) 1,
        (carryBit α t : ℝ) * (carryBit α (t + δ) : ℝ) =
      max 0 (α - δ) + max 0 (α + δ - 1) := by
  have hset := jointCarrySet_eq_union hα0 hα1 hδ0 hδ1
  have hjmeas : MeasurableSet (jointCarrySet α δ) := by
    rw [hset]
    exact measurableSet_Ico.union measurableSet_Ico
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ico (fun t ht => ?_)]
  · rw [integral_indicator_const (1 : ℝ) hjmeas]
    rw [measureReal_restrict_apply hjmeas]
    have hsub : jointCarrySet α δ ⊆ Ico (0 : ℝ) 1 := by
      intro t ht
      exact ht.1
    rw [inter_eq_left.mpr hsub]
    simpa using jointCarrySet_measureReal hα0 hα1 hδ0 hδ1
  · simp only [jointCarrySet, Set.mem_setOf_eq, Set.indicator]
    by_cases hfirst : carryBit α t = 1
    · by_cases hsecond : carryBit α (t + δ) = 1
      · simp [ht, hfirst, hsecond]
      · have hzero : carryBit α (t + δ) = 0 := by
          rw [carryBit] at hsecond ⊢
          split_ifs with h <;> simp_all
        simp [ht, hfirst, hzero]
    · have hzero : carryBit α t = 0 := by
        rw [carryBit] at hfirst ⊢
        split_ifs with h <;> simp_all
      simp [ht, hzero]

/-- The overlap kernel appearing in the Sturmian covariance formula. -/
def overlapKernel (α δ : ℝ) : ℝ :=
  max 0 (α - δ) + max 0 (α + δ - 1)

/-- Covariance written as joint success probability minus the product of the two stationary
marginal means. -/
noncomputable def carryCovariance (α δ : ℝ) : ℝ :=
  (∫ t in Ico (0 : ℝ) 1,
      (carryBit α t : ℝ) * (carryBit α (t + δ) : ℝ)) - α ^ 2

theorem carryCovariance_eq {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    carryCovariance α δ = overlapKernel α δ - α ^ 2 := by
  rw [carryCovariance, jointCarry_integral hα0 hα1 hδ0 hδ1]
  rfl

end LeanProofs.TwoBaseIntegerExponent
