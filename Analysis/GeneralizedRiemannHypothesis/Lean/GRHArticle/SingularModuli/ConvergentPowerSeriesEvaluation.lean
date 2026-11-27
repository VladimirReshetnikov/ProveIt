import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Convergent evaluation of complex formal series

Absolute convergence gives evaluation rules for the formal product and
the two substitutions used in a Hecke orbit.
-/

namespace GRHArticle.SingularModuli

open scoped PowerSeries Topology NNReal ENNReal
open PowerSeries

/-- The formal series `F` sums absolutely to `x` at `u`. -/
structure PowerSeriesValue (F : ℂ⟦X⟧) (u x : ℂ) : Prop where
  hasSum : HasSum (fun n ↦ F.coeff n * u ^ n) x
  summable_norm : Summable (fun n ↦ ‖F.coeff n * u ^ n‖)

namespace PowerSeriesValue

variable {A B : ℂ⟦X⟧} {u x y : ℂ}

theorem C (a u : ℂ) : PowerSeriesValue (PowerSeries.C a) u a := by
  have he (n : ℕ) : (PowerSeries.C a).coeff n * u ^ n = if n = 0 then a else 0 := by
    by_cases hn : n = 0 <;> simp [coeff_C, hn]
  constructor
  · simpa only [he] using hasSum_ite_eq (0 : ℕ) a
  · have hn (n : ℕ) : ‖(PowerSeries.C a).coeff n * u ^ n‖ =
        if n = 0 then ‖a‖ else 0 := by rw [he]; split_ifs <;> simp
    simpa only [hn] using (hasSum_ite_eq (0 : ℕ) ‖a‖).summable

theorem one (u : ℂ) : PowerSeriesValue 1 u 1 := by simpa using C 1 u

theorem X_pow (d : ℕ) (u : ℂ) : PowerSeriesValue (PowerSeries.X ^ d) u (u ^ d) := by
  have he (n : ℕ) : ((PowerSeries.X : ℂ⟦X⟧) ^ d).coeff n * u ^ n =
      if n = d then u ^ d else 0 := by
    by_cases hn : n = d <;> simp [coeff_X_pow, hn]
  constructor
  · simpa only [he] using hasSum_ite_eq d (u ^ d)
  · have hn (n : ℕ) : ‖((PowerSeries.X : ℂ⟦X⟧) ^ d).coeff n * u ^ n‖ =
        if n = d then ‖u ^ d‖ else 0 := by rw [he]; split_ifs <;> simp
    simpa only [hn] using (hasSum_ite_eq d ‖u ^ d‖).summable

theorem at_zero (F : ℂ⟦X⟧) : PowerSeriesValue F 0 (F.coeff 0) := by
  have he (n : ℕ) : F.coeff n * (0 : ℂ) ^ n =
      if n = 0 then F.coeff 0 else 0 := by
    by_cases hn : n = 0 <;> simp [hn]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hasSum_ite_eq (0 : ℕ) (F.coeff 0)
  · have hn (n : ℕ) : ‖F.coeff n * (0 : ℂ) ^ n‖ =
        if n = 0 then ‖F.coeff 0‖ else 0 := by rw [he]; split_ifs <;> simp
    simpa only [hn] using (hasSum_ite_eq (0 : ℕ) ‖F.coeff 0‖).summable

theorem add (ha : PowerSeriesValue A u x) (hb : PowerSeriesValue B u y) :
    PowerSeriesValue (A + B) u (x + y) := by
  constructor
  · simpa only [map_add, add_mul] using ha.hasSum.add hb.hasSum
  · refine (ha.summable_norm.add hb.summable_norm).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro n
    simp only [map_add, add_mul]
    exact norm_add_le _ _

theorem sub (ha : PowerSeriesValue A u x) (hb : PowerSeriesValue B u y) :
    PowerSeriesValue (A - B) u (x - y) := by
  constructor
  · simpa only [map_sub, sub_mul] using ha.hasSum.sub hb.hasSum
  · refine (ha.summable_norm.add hb.summable_norm).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro n
    simp only [map_sub, sub_mul]
    exact norm_sub_le _ _

theorem mul (ha : PowerSeriesValue A u x) (hb : PowerSeriesValue B u y) :
    PowerSeriesValue (A * B) u (x * y) := by
  have he (n : ℕ) : (A * B).coeff n * u ^ n =
      ∑ ij ∈ Finset.antidiagonal n, (A.coeff ij.1 * u ^ ij.1) * (B.coeff ij.2 * u ^ ij.2) := by
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hij, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha.summable_norm hb.summable_norm
  have ht := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    ha.summable_norm hb.summable_norm
  rw [ha.hasSum.tsum_eq, hb.hasSum.tsum_eq] at ht
  constructor
  · rw [ht]
    exact hs.of_norm.hasSum.congr_fun fun n ↦ he n
  · exact hs.congr fun n ↦ congrArg norm (he n).symm

theorem pow (ha : PowerSeriesValue A u x) (n : ℕ) :
    PowerSeriesValue (A ^ n) u (x ^ n) := by
  induction n with
  | zero => simpa using one u
  | succ n h => simpa only [pow_succ] using h.mul ha

theorem prod {α : Type*} (s : Finset α) (F : α → ℂ⟦X⟧) (f : α → ℂ)
    (h : ∀ i ∈ s, PowerSeriesValue (F i) u (f i)) :
    PowerSeriesValue (∏ i ∈ s, F i) u (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one u
  | insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (h i (Finset.mem_insert_self i s)).mul (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem rescale {a : ℂ} (h : PowerSeriesValue A (a * u) x) :
    PowerSeriesValue (PowerSeries.rescale a A) u x := by
  have he (n : ℕ) : (PowerSeries.rescale a A).coeff n * u ^ n = A.coeff n * (a * u) ^ n := by
    rw [coeff_rescale, mul_pow]
    ring
  exact ⟨h.hasSum.congr_fun fun n ↦ he n, h.summable_norm.congr fun n ↦ congrArg norm (he n).symm⟩

theorem expand {d : ℕ} (hd : d ≠ 0) (h : PowerSeriesValue A (u ^ d) x) :
    PowerSeriesValue (PowerSeries.expand d hd A) u x := by
  let f (n : ℕ) := (PowerSeries.expand d hd A).coeff n * u ^ n
  have hi : Function.Injective (fun n : ℕ ↦ d * n) := fun _ _ he ↦ Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero hd) he
  have hzero (n : ℕ) (hn : n ∉ Set.range (fun i : ℕ ↦ d * i)) : f n = 0 := by
    have hnd : ¬ d ∣ n := fun ⟨c, hc⟩ ↦ hn ⟨c, hc.symm⟩
    simp only [f, coeff_expand_of_not_dvd d hd _ hnd, zero_mul]
  have he (n : ℕ) : f (d * n) = A.coeff n * (u ^ d) ^ n := by
    simp only [f, coeff_expand_mul, pow_mul]
  constructor
  · exact (hi.hasSum_iff hzero).mp (h.hasSum.congr_fun fun n ↦ he n)
  · exact ((hi.hasSum_iff (f := fun n ↦ ‖f n‖) (fun n hn ↦ by rw [hzero n hn, norm_zero])).mp
      (h.summable_norm.hasSum.congr_fun fun n ↦ congrArg norm (he n))).summable

/-- A larger radius of convergence supplies the absolute convergence needed
for formal multiplication at the smaller radius. -/
theorem of_hasSum_of_norm_lt {v b : ℂ}
    (hu : HasSum (fun n ↦ A.coeff n * u ^ n) x)
    (hv : HasSum (fun n ↦ A.coeff n * v ^ n) b) (hlt : ‖u‖ < ‖v‖) :
    PowerSeriesValue A u x := by
  refine ⟨hu, ?_⟩
  let g (n : ℕ) := A.coeff n * v ^ n
  have hm : Bornology.IsBounded (Set.range g) :=
    Metric.isBounded_range_of_tendsto g hv.summable.tendsto_atTop_zero
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hm
  have hnorm (n : ℕ) : ‖g n‖ ≤ C + ‖g 0‖ := by
    calc
      ‖g n‖ ≤ ‖g n - g 0‖ + ‖g 0‖ := norm_le_norm_sub_add _ _
      _ ≤ C + ‖g 0‖ := by
        have h := hC n 0
        rw [dist_eq_norm] at h
        gcongr
  have hv₀ : v ≠ 0 := norm_ne_zero_iff.mp (lt_of_le_of_lt (norm_nonneg _) hlt).ne'
  have hratio : ‖u / v‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hv₀)]
    exact hlt
  have hs := (summable_geometric_of_lt_one (norm_nonneg _) hratio).mul_left (C + ‖g 0‖)
  refine hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  calc
    ‖A.coeff n * u ^ n‖ = ‖g n * (u / v) ^ n‖ := by
      congr 1
      change A.coeff n * u ^ n = (A.coeff n * v ^ n) * (u / v) ^ n
      rw [mul_assoc, ← mul_pow, ← mul_div_assoc, mul_div_cancel_left₀ u hv₀]
    _ = ‖g n‖ * ‖u / v‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hnorm n) (by positivity)

end PowerSeriesValue

/-- Power series with identical convergent evaluations on a neighborhood
of zero have the same formal coefficients. -/
theorem eq_of_powerSeriesValues {A B : ℂ⟦X⟧} {r : ℝ} (hr : 0 < r)
    (h : ∀ u : ℂ, ‖u‖ < r → ∃ x, PowerSeriesValue A u x ∧ PowerSeriesValue B u x) :
    A = B := by
  let R : ℝ≥0 := ⟨r / 2, (half_pos hr).le⟩
  have hR : (R : ℝ) < r := half_lt_self hr
  have hRpos : (0 : ℝ) < R := half_pos hr
  let f (u : ℂ) := ∑' n, A.coeff n * u ^ n
  have hA (u : ℂ) (hu : ‖u‖ < r) : PowerSeriesValue A u (f u) := by
    obtain ⟨x, ha, _⟩ := h u hu
    rwa [show f u = x from ha.hasSum.tsum_eq]
  have hB (u : ℂ) (hu : ‖u‖ < r) : PowerSeriesValue B u (f u) := by
    obtain ⟨x, ha, hb⟩ := h u hu
    rwa [show f u = x from ha.hasSum.tsum_eq]
  have hball (P : ℂ⟦X⟧) (hP : ∀ u : ℂ, ‖u‖ < r → PowerSeriesValue P u (f u)) :
      HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ P.coeff n)) 0 (R : ℝ≥0∞) := by
    refine ⟨?_, by exact_mod_cast hRpos, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      have hnorm : ‖((R : ℝ) : ℂ)‖ = R := by simp
      have hs := (hP (R : ℝ) (hnorm.trans_lt hR)).summable_norm
      simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, hnorm] using hs
    · intro u hu
      have hu' : ‖u‖ < R := by
        rw [mem_eball_zero_iff] at hu
        exact_mod_cast hu
      simpa [FormalMultilinearSeries.ofScalars, Finset.prod_const, zero_add] using (hP u (hu'.trans hR)).hasSum
  have he := (hball A hA).hasFPowerSeriesAt.eq_formalMultilinearSeries (hball B hB).hasFPowerSeriesAt
  ext n
  exact congrFun ((FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ) he) n

end GRHArticle.SingularModuli
