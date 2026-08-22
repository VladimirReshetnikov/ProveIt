import IntegerPoints.ExponentialSums
import IntegerPoints.Lemma3
import IntegerPoints.BombieriIwaniec
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Zhai–Cao, Lemma 6 (Fouvry–Iwaniec, Lemma 1)

`𝒜(M, N; Δ) = #{(m, m̃, n, ñ) : |(m̃/m)^α − (ñ/n)^β| < Δ} ≪ MN log 2MN + Δ M²N²`.

Proof (Fouvry–Iwaniec, *Exponential sums with monomials*, Lemma 1).  Sort
the quadruples into classes by `μ = gcd(m, m̃)` and `ν = gcd(n, ñ)`.  Within a
class the points `(m̃/m)^α` are distinct reduced fractions raised to the
power `α`, hence spaced by `≥ c(α) μ²/M²`, and similarly for `(ñ/n)^β`; so by
the box principle a class contains at most
`min{ (M/μ)²(1 + Δ (N/ν)²), (N/ν)²(1 + Δ (M/μ)²) } ≪ min{(M/μ)², (N/ν)²} + Δ (MN/(μν))²`
quadruples.  Summing over `μ, ν` gives the claim.

Stage A: the spacing and counting lemmas.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace FI

/-! ### Spacing of powers on `[1/2, 2]` -/

/-- The constant `c(α) = |α| min(2^{α-1}, 2^{1-α})`, a lower bound for `|α x^{α-1}|` on
`[1/2, 2]`. -/
noncomputable def cpow (α : ℝ) : ℝ := |α| * min ((2 : ℝ) ^ (α - 1)) ((2 : ℝ) ^ (1 - α))

theorem cpow_pos {α : ℝ} (hα : α ≠ 0) : 0 < cpow α := by
  unfold cpow
  exact mul_pos (abs_pos.2 hα) (lt_min (by positivity) (by positivity))

/-- `|α x^{α-1}| ≥ c(α)` for `x ∈ [1/2, 2]`. -/
theorem cpow_le_abs_deriv {α x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 2) :
    cpow α ≤ |α * x ^ (α - 1)| := by
  unfold cpow
  have hx0 : 0 < x := by linarith
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases le_or_gt 0 (α - 1) with h | h
  · -- increasing in `x`: minimum at `x = 1/2`
    calc min ((2 : ℝ) ^ (α - 1)) ((2 : ℝ) ^ (1 - α)) ≤ (2 : ℝ) ^ (1 - α) := min_le_right _ _
      _ = (1 / 2 : ℝ) ^ (α - 1) := by
          rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num)]
          congr 1
          ring
      _ ≤ x ^ (α - 1) := Real.rpow_le_rpow (by norm_num) hx1 h
  · -- decreasing in `x`: minimum at `x = 2`
    calc min ((2 : ℝ) ^ (α - 1)) ((2 : ℝ) ^ (1 - α)) ≤ (2 : ℝ) ^ (α - 1) := min_le_left _ _
      _ ≤ x ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hx0 hx2 h.le

/-- Spacing of the power map: `|x^α − x'^α| ≥ c(α) |x − x'|` on `[1/2, 2]`. -/
theorem abs_rpow_sub_ge {α x x' : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 2) (hx1' : 1 / 2 ≤ x')
    (hx2' : x' ≤ 2) : cpow α * |x - x'| ≤ |x ^ α - x' ^ α| := by
  rcases eq_or_ne x x' with h | h
  · simp [h]
  wlog hlt : x' < x generalizing x x'
  · have := this hx1' hx2' hx1 hx2 h.symm (lt_of_le_of_ne (not_lt.1 hlt) h)
    rwa [abs_sub_comm, abs_sub_comm (x' ^ α)] at this
  have hcont : ContinuousOn (fun t : ℝ => t ^ α) (Set.Icc x' x) :=
    (continuousOn_id.rpow_const fun t ht => Or.inl (show t ≠ 0 by linarith [ht.1])).congr
      fun t _ => rfl
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ α) (Set.Ioo x' x) := by
    intro t ht
    exact ((hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (fun t : ℝ => t ^ α) hlt hcont hdiff
  have hcd : deriv (fun t : ℝ => t ^ α) c = α * c ^ (α - 1) :=
    (hasDerivAt_rpow_const (Or.inl (by linarith [hc.1]))).deriv
  rw [hcd] at hc'
  have hslope : x ^ α - x' ^ α = α * c ^ (α - 1) * (x - x') := by
    rw [hc', div_mul_cancel₀ _ (by linarith)]
  rw [hslope, abs_mul]
  exact mul_le_mul_of_nonneg_right (cpow_le_abs_deriv (by linarith [hc.1]) (by linarith [hc.2]))
    (abs_nonneg _)

/-! ### Reduced fractions with a fixed gcd are well spaced -/

/-- Two distinct fractions `m̃/m ≠ m̃'/m'` with `gcd(m, m̃) = gcd(m', m̃') = μ` differ by at least
`μ² / (m m')`. -/
theorem frac_spacing {m m' mt mt' μ : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hg : Nat.gcd m mt = μ) (hg' : Nat.gcd m' mt' = μ)
    (hne : (mt : ℝ) / m ≠ (mt' : ℝ) / m') :
    (μ : ℝ) ^ 2 / ((m : ℝ) * m') ≤ |(mt : ℝ) / m - (mt' : ℝ) / m'| := by
  have hμm : μ ∣ m := hg ▸ Nat.gcd_dvd_left m mt
  have hμmt : μ ∣ mt := hg ▸ Nat.gcd_dvd_right m mt
  have hμm' : μ ∣ m' := hg' ▸ Nat.gcd_dvd_left m' mt'
  have hμmt' : μ ∣ mt' := hg' ▸ Nat.gcd_dvd_right m' mt'
  obtain ⟨a, ha⟩ := hμm
  obtain ⟨b, hb⟩ := hμmt
  obtain ⟨a', ha'⟩ := hμm'
  obtain ⟨b', hb'⟩ := hμmt'
  have hμ0 : 0 < μ := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h; simp at ha; omega
    · exact h
  -- the integer `D = b a' - a b'` is nonzero
  have hD : (b : ℤ) * a' - a * b' ≠ 0 := by
    intro h0
    apply hne
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
    rw [div_eq_div_iff hm0 hm0']
    have : (b : ℝ) * a' = a * b' := by
      have h1 : ((b : ℤ) * a' : ℤ) = (a * b' : ℤ) := by linarith
      exact_mod_cast h1
    rw [hb, hb', ha, ha']
    push_cast
    linear_combination ((μ : ℝ) ^ 2) * this
  have hD1 : (1 : ℝ) ≤ |((b : ℝ) * a' - a * b')| := by
    have : (1 : ℤ) ≤ |(b : ℤ) * a' - a * b'| := Int.one_le_abs hD
    have h' : ((1 : ℤ) : ℝ) ≤ ((|(b : ℤ) * a' - a * b'| : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0' : (0 : ℝ) < m' := by exact_mod_cast hm'
  rw [div_sub_div _ _ hm0.ne' hm0'.ne', abs_div, abs_of_pos (mul_pos hm0 hm0'),
    div_le_div_iff_of_pos_right (mul_pos hm0 hm0')]
  have e : (mt : ℝ) * m' - m * mt' = (μ : ℝ) ^ 2 * ((b : ℝ) * a' - a * b') := by
    rw [hb, hb', ha, ha']
    push_cast
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (μ : ℝ) ^ 2)]
  nlinarith [hD1, (by positivity : (0 : ℝ) < (μ : ℝ) ^ 2)]

/-! ### Counting a well-spaced set inside an interval -/

/-- A finite set of reals inside `(p - Δ, p + Δ)` whose distinct points are at least `δ` apart
has at most `2Δ/δ + 1` elements. -/
theorem card_le_of_spaced (Y : Finset ℝ) (p Δ δ : ℝ) (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hY : ∀ y ∈ Y, |y - p| < Δ) (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → δ ≤ |y - y'|) :
    (Y.card : ℝ) ≤ 2 * Δ / δ + 1 := by
  classical
  set K : ℕ := ⌊2 * Δ / δ⌋₊ + 1 with hK
  set sh : ℝ → ℕ := fun y => ⌊(y - (p - Δ)) / δ⌋₊ with hsh
  have hmaps : ∀ y ∈ Y, sh y ∈ Finset.range K := by
    intro y hy
    have h := abs_lt.1 (hY y hy)
    rw [Finset.mem_range, hK, Nat.lt_succ_iff, hsh]
    apply Nat.floor_le_floor
    rw [div_le_div_iff_of_pos_right hδ]
    linarith
  have hinj : Set.InjOn sh Y := by
    intro y hy y' hy' hs
    by_contra hne
    have hd := hsep y hy y' hy' hne
    have h1 := Nat.floor_le (by
      have := abs_lt.1 (hY y hy)
      rw [div_nonneg_iff]; left; constructor <;> linarith : 0 ≤ (y - (p - Δ)) / δ)
    have h2 := Nat.lt_floor_add_one ((y - (p - Δ)) / δ)
    have h1' := Nat.floor_le (by
      have := abs_lt.1 (hY y' hy')
      rw [div_nonneg_iff]; left; constructor <;> linarith : 0 ≤ (y' - (p - Δ)) / δ)
    have h2' := Nat.lt_floor_add_one ((y' - (p - Δ)) / δ)
    rw [hsh] at hs
    simp only at hs
    rw [hs] at h1 h2
    rw [le_div_iff₀ hδ] at h1 h1'
    rw [div_lt_iff₀ hδ] at h2 h2'
    have : |y - y'| < δ := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hcard : Y.card ≤ K := by
    calc Y.card = (Y.image sh).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range K).card := Finset.card_le_card (Finset.image_subset_iff.2 hmaps)
      _ = K := Finset.card_range K
  calc (Y.card : ℝ) ≤ K := by exact_mod_cast hcard
    _ = (⌊2 * Δ / δ⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
    _ ≤ 2 * Δ / δ + 1 := by
        have := Nat.floor_le (by positivity : 0 ≤ 2 * Δ / δ)
        linarith

/-! ### Stage B1: the sums over `μ` and `ν` -/

/-- Telescoping: `∑_{k < ν ≤ V} (1/(ν-1) - 1/ν) = 1/k - 1/V` for `k ≤ V`. -/
theorem sum_telescope (k : ℕ) :
    ∀ V : ℕ, k ≤ V → ∑ ν ∈ Finset.Ioc k V, (1 / ((ν : ℝ) - 1) - 1 / ν) = 1 / k - 1 / V := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hkV ih =>
    rw [Finset.sum_Ioc_succ_top hkV, ih]
    push_cast
    ring

/-- The tail `∑_{ν ∈ [1, V], ν > T} 1/ν² ≤ 2/T` for `T ≥ 1`. -/
theorem sum_inv_sq_tail (V : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2) ≤ 2 / T := by
  classical
  set k : ℕ := ⌊T⌋₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_floor_iff]
    exact hT
  have hkT : (k : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hTk : T < k + 1 := Nat.lt_floor_add_one T
  have hsub : (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)) ⊆ Finset.Ioc k V := by
    intro ν hν
    rw [Finset.mem_filter, Finset.mem_Icc] at hν
    rw [Finset.mem_Ioc]
    refine ⟨?_, hν.1.2⟩
    have : (k : ℝ) < ν := lt_of_le_of_lt hkT hν.2
    exact_mod_cast this
  have hterm : ∀ ν ∈ Finset.Ioc k V, 1 / ((ν : ℝ) ^ 2) ≤ 1 / ((ν : ℝ) - 1) - 1 / ν := by
    intro ν hν
    rw [Finset.mem_Ioc] at hν
    have hν2 : (2 : ℝ) ≤ ν := by exact_mod_cast (by omega : 2 ≤ ν)
    have hν1 : (ν : ℝ) - 1 ≠ 0 := by linarith
    have hνne : (ν : ℝ) ≠ 0 := by linarith
    have e : 1 / ((ν : ℝ) - 1) - 1 / ν = 1 / ((ν : ℝ) * (ν - 1)) := by
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  rcases le_or_gt k V with hkV | hkV
  · have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    calc ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2)
        ≤ ∑ ν ∈ Finset.Ioc k V, 1 / ((ν : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ ν ∈ Finset.Ioc k V, (1 / ((ν : ℝ) - 1) - 1 / ν) := Finset.sum_le_sum hterm
      _ = 1 / k - 1 / V := sum_telescope k V hkV
      _ ≤ 1 / k := by linarith [show (0 : ℝ) ≤ 1 / V by positivity]
      _ ≤ 2 / T := by
          rw [div_le_div_iff₀ (by positivity) (by linarith)]
          linarith
  · have : (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)) = ∅ := by
      apply Finset.subset_empty.1
      refine hsub.trans ?_
      rw [Finset.Ioc_eq_empty (by omega)]
    rw [this, Finset.sum_empty]
    positivity

/-- `∑_{ν=1}^{V} 1/ν² ≤ 3`. -/
theorem sum_inv_sq_le_three (V : ℕ) : ∑ ν ∈ Finset.Icc 1 V, 1 / ((ν : ℝ) ^ 2) ≤ 3 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 V) (fun ν : ℕ => (1 : ℝ) < (ν : ℝ))]
  have h1 : ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ (1 : ℝ) < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2) ≤ 1 := by
    have hsub : (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ (1 : ℝ) < (ν : ℝ)) ⊆ {1} := by
      intro ν hν
      rw [Finset.mem_filter, Finset.mem_Icc] at hν
      rw [Finset.mem_singleton]
      have : (ν : ℝ) ≤ 1 := not_lt.1 hν.2
      have : ν ≤ 1 := by exact_mod_cast this
      omega
    calc ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ (1 : ℝ) < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2)
        ≤ ∑ ν ∈ ({1} : Finset ℕ), 1 / ((ν : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  have h2 := sum_inv_sq_tail V 1 le_rfl
  linarith

/-- `∑_{ν=1}^{V} min(a, N²/ν²) ≤ 4 √a N`. -/
theorem sum_min_le (V : ℕ) (a N : ℝ) (ha : 0 < a) (hN : 0 < N) :
    ∑ ν ∈ Finset.Icc 1 V, min a (N ^ 2 / (ν : ℝ) ^ 2) ≤ 4 * Real.sqrt a * N := by
  classical
  set T : ℝ := N / Real.sqrt a with hT
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hT0 : 0 < T := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 V) (fun ν : ℕ => T < (ν : ℝ))]
  -- the small `ν`
  have hsmall : ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ)), min a (N ^ 2 / (ν : ℝ) ^ 2)
      ≤ Real.sqrt a * N := by
    have hsub : (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ)) ⊆ Finset.Icc 1 ⌊T⌋₊ := by
      intro ν hν
      rw [Finset.mem_filter, Finset.mem_Icc] at hν
      rw [Finset.mem_Icc]
      refine ⟨hν.1.1, ?_⟩
      rw [Nat.le_floor_iff hT0.le]
      exact not_lt.1 hν.2
    have hcard : (((Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ))).card : ℝ) ≤ T := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      calc (((Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ))).card : ℝ) ≤ ⌊T⌋₊ := by
            exact_mod_cast this
        _ ≤ T := Nat.floor_le hT0.le
    calc ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ)), min a (N ^ 2 / (ν : ℝ) ^ 2)
        ≤ ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ)), a :=
          Finset.sum_le_sum fun ν _ => min_le_left _ _
      _ = ((Finset.Icc 1 V).filter (fun ν : ℕ => ¬ T < (ν : ℝ))).card * a := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T * a := mul_le_mul_of_nonneg_right hcard ha.le
      _ = N / Real.sqrt a * (Real.sqrt a * Real.sqrt a) := by rw [hT, hsa2]
      _ = Real.sqrt a * N := by
          rw [← mul_assoc, div_mul_cancel₀ _ hsa.ne']
          ring
  -- the large `ν`
  have hlarge : ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), min a (N ^ 2 / (ν : ℝ) ^ 2)
      ≤ 3 * Real.sqrt a * N := by
    have h1 : ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), min a (N ^ 2 / (ν : ℝ) ^ 2)
        ≤ N ^ 2 * ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ν _ => ?_
      rw [mul_one_div]
      exact min_le_right _ _
    rcases le_or_gt 1 T with hT1 | hT1
    · have := sum_inv_sq_tail V T hT1
      calc _ ≤ N ^ 2 * (2 / T) := h1.trans (mul_le_mul_of_nonneg_left this (by positivity))
        _ = 2 * Real.sqrt a * N := by
            rw [hT, div_div_eq_mul_div, mul_div_assoc', div_eq_iff hN.ne']
            ring
        _ ≤ 3 * Real.sqrt a * N := by nlinarith [mul_pos hsa hN]
    · -- `N < √a`
      have hN' : N ≤ Real.sqrt a := by
        rw [hT, div_lt_iff₀ hsa, one_mul] at hT1
        exact hT1.le
      have h2 : ∑ ν ∈ (Finset.Icc 1 V).filter (fun ν : ℕ => T < (ν : ℝ)), 1 / ((ν : ℝ) ^ 2) ≤ 3 :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)) (sum_inv_sq_le_three V)
      calc _ ≤ N ^ 2 * 3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ ≤ 3 * Real.sqrt a * N := by nlinarith
  linarith

/-- `∑_{μ=1}^{U} 1/μ ≤ 1 + log U`. -/
theorem sum_inv_le (U : ℕ) : ∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) ≤ 1 + Real.log U := by
  have h := harmonic_le_one_add_log U
  have e : ∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) = (harmonic U : ℝ) := by
    rw [harmonic, Rat.cast_sum]
    rw [show Finset.Icc 1 U = Finset.Ico 1 (U + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [add_comm, one_div]
  rw [e]
  exact h

/-- The double sum `∑_{μ,ν} min(M²/μ², N²/ν²) ≤ 4 M N (1 + log U)`. -/
theorem sum_sum_min_le (U V : ℕ) (M N : ℝ) (hM : 0 < M) (hN : 0 < N) :
    ∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V, min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2) ≤
      4 * M * N * (1 + Real.log U) := by
  calc ∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V, min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2)
      ≤ ∑ μ ∈ Finset.Icc 1 U, 4 * Real.sqrt (M ^ 2 / (μ : ℝ) ^ 2) * N := by
        refine Finset.sum_le_sum fun μ hμ => ?_
        have hμ0 : (0 : ℝ) < μ := by
          rw [Finset.mem_Icc] at hμ
          exact_mod_cast hμ.1
        exact sum_min_le V _ N (by positivity) hN
    _ = ∑ μ ∈ Finset.Icc 1 U, 4 * M * N * (1 / (μ : ℝ)) := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        have hμ0 : (0 : ℝ) < μ := by
          rw [Finset.mem_Icc] at hμ
          exact_mod_cast hμ.1
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq hM.le, Real.sqrt_sq hμ0.le]
        ring
    _ = 4 * M * N * ∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * M * N * (1 + Real.log U) :=
        mul_le_mul_of_nonneg_left (sum_inv_le U) (by positivity)

/-! ### Stage B2: class sizes -/

/-- The multiples of `μ ≥ 1` in `[M, 2M]` number at most `2M/μ`. -/
theorem card_multiples_le (M : ℝ) (hM : 1 ≤ M) (μ : ℕ) (hμ : 1 ≤ μ) :
    (((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)).card : ℝ) ≤ 2 * M / μ := by
  classical
  have hμ0 : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hmaps : ∀ m ∈ (closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m),
      m / μ ∈ Finset.Icc 1 ⌊2 * M / μ⌋₊ := by
    intro m hm
    rw [Finset.mem_filter, closedRange, Finset.mem_Icc] at hm
    rw [Finset.mem_Icc]
    have hm1 : 1 ≤ m := by
      have : 1 ≤ ⌈M⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
      omega
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hm1 hm.2) hμ
    · rw [Nat.le_floor_iff (by positivity), Nat.cast_div hm.2 hμ0.ne']
      have : (m : ℝ) ≤ 2 * M := (Nat.le_floor_iff (by linarith)).1 hm.1.2
      exact div_le_div_of_nonneg_right this hμ0.le
  have hinj : Set.InjOn (fun m : ℕ => m / μ) ((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)) := by
    intro m hm m' hm' h
    replace hm : m ∈ (closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m) := hm
    replace hm' : m' ∈ (closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m) := hm'
    rw [Finset.mem_filter] at hm hm'
    have h1 := Nat.div_mul_cancel hm.2
    have h2 := Nat.div_mul_cancel hm'.2
    simp only at h
    rw [← h1, ← h2, h]
  calc (((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)).card : ℝ)
      = (((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)).image (fun m : ℕ => m / μ)).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Finset.Icc 1 ⌊2 * M / μ⌋₊).card := by
        exact_mod_cast Finset.card_le_card (Finset.image_subset_iff.2 hmaps)
    _ = ⌊2 * M / μ⌋₊ := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ 2 * M / μ := Nat.floor_le (by positivity)

/-- The class of pairs `(m, m̃)` in `[M, 2M]²` with `gcd(m, m̃) = μ`. -/
noncomputable def cls (M : ℝ) (μ : ℕ) : Finset (ℕ × ℕ) :=
  (closedRange M (2 * M) ×ˢ closedRange M (2 * M)).filter (fun p => Nat.gcd p.1 p.2 = μ)

theorem card_cls_le (M : ℝ) (hM : 1 ≤ M) (μ : ℕ) (hμ : 1 ≤ μ) :
    ((cls M μ).card : ℝ) ≤ (2 * M / μ) ^ 2 := by
  classical
  have hsub : cls M μ ⊆ (closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m) ×ˢ
      (closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m) := by
    intro p hp
    rw [cls, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨hp.1.1, hp.2 ▸ Nat.gcd_dvd_left _ _⟩, ⟨hp.1.2, hp.2 ▸ Nat.gcd_dvd_right _ _⟩⟩
  have h := card_multiples_le M hM μ hμ
  calc ((cls M μ).card : ℝ) ≤ ((((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)) ×ˢ
        ((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (((closedRange M (2 * M)).filter (fun m : ℕ => μ ∣ m)).card : ℝ) ^ 2 := by
        rw [Finset.card_product]
        push_cast
        ring
    _ ≤ (2 * M / μ) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h


/-! ### Stage C: one class -/

theorem mem_cls {N : ℝ} {ν : ℕ} {q : ℕ × ℕ} (hq : q ∈ cls N ν) :
    q.1 ∈ closedRange N (2 * N) ∧ q.2 ∈ closedRange N (2 * N) ∧ Nat.gcd q.1 q.2 = ν := by
  simp only [cls, Finset.mem_filter, Finset.mem_product] at hq
  exact ⟨hq.1.1, hq.1.2, hq.2⟩

/-- Elements of `closedRange N (2N)` lie in `[N, 2N]`. -/
theorem mem_closedRange_bounds {N : ℝ} (hN : 1 ≤ N) {n : ℕ} (hn : n ∈ closedRange N (2 * N)) :
    N ≤ n ∧ (n : ℝ) ≤ 2 * N := by
  rw [closedRange, Finset.mem_Icc] at hn
  exact ⟨le_trans (Nat.le_ceil N) (by exact_mod_cast hn.1),
    (Nat.le_floor_iff (by linarith)).1 hn.2⟩

/-- The fraction `ñ/n` with `n, ñ ∈ [N, 2N]` lies in `[1/2, 2]`. -/
theorem frac_bounds {N : ℝ} (hN : 1 ≤ N) {n nt : ℕ} (hn : n ∈ closedRange N (2 * N))
    (hnt : nt ∈ closedRange N (2 * N)) : 1 / 2 ≤ (nt : ℝ) / n ∧ (nt : ℝ) / n ≤ 2 := by
  obtain ⟨h1, h2⟩ := mem_closedRange_bounds hN hn
  obtain ⟨h3, h4⟩ := mem_closedRange_bounds hN hnt
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · rw [le_div_iff₀ hn0]; linarith
  · rw [div_le_iff₀ hn0]; linarith

/-- If `gcd(n, ñ) = gcd(n', ñ') = ν ≥ 1`, `n > 0` and `ñ n' = ñ' n`, then `(n, ñ) = (n', ñ')`. -/
theorem eq_of_cross_mul {n nt n' nt' ν : ℕ} (hν : 1 ≤ ν) (hn : 0 < n) (hg : Nat.gcd n nt = ν)
    (hg' : Nat.gcd n' nt' = ν) (h : nt * n' = nt' * n) : n = n' ∧ nt = nt' := by
  have hν0 : 0 < ν := hν
  have hc : Nat.Coprime (n / ν) (nt / ν) := by
    have := Nat.coprime_div_gcd_div_gcd (m := n) (n := nt) (by rw [hg]; exact hν0)
    rwa [hg] at this
  have hc' : Nat.Coprime (n' / ν) (nt' / ν) := by
    have := Nat.coprime_div_gcd_div_gcd (m := n') (n := nt') (by rw [hg']; exact hν0)
    rwa [hg'] at this
  have ha : n = ν * (n / ν) := (Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_left n nt)).symm
  have hb : nt = ν * (nt / ν) := (Nat.mul_div_cancel' (hg ▸ Nat.gcd_dvd_right n nt)).symm
  have ha' : n' = ν * (n' / ν) := (Nat.mul_div_cancel' (hg' ▸ Nat.gcd_dvd_left n' nt')).symm
  have hb' : nt' = ν * (nt' / ν) := (Nat.mul_div_cancel' (hg' ▸ Nat.gcd_dvd_right n' nt')).symm
  set a := n / ν with ha_def
  set b := nt / ν with hb_def
  set a' := n' / ν with ha'_def
  set b' := nt' / ν with hb'_def
  have hab : b * a' = b' * a := by
    have h2 : (ν * ν) * (b * a') = (ν * ν) * (b' * a) := by
      calc (ν * ν) * (b * a') = (ν * b) * (ν * a') := by ring
        _ = nt * n' := by rw [← hb, ← ha']
        _ = nt' * n := h
        _ = (ν * b') * (ν * a) := by rw [← hb', ← ha]
        _ = (ν * ν) * (b' * a) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have h1 : a ∣ a' * b := by
    rw [mul_comm, hab, mul_comm]
    exact dvd_mul_right a b'
  have h2 : a' ∣ a * b' := by
    rw [mul_comm, ← hab, mul_comm]
    exact dvd_mul_right a' b
  have haa : a = a' := Nat.dvd_antisymm (hc.dvd_of_dvd_mul_right h1) (hc'.dvd_of_dvd_mul_right h2)
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, mul_zero] at ha; omega
    · exact h0
  have hbb : b = b' := by
    rw [haa] at hab
    exact Nat.eq_of_mul_eq_mul_right (haa ▸ ha0) hab
  constructor
  · rw [ha, ha', haa]
  · rw [hb, hb', hbb]

/-- In a class, distinct pairs give fractions spaced by `ν²/(4N²)`. -/
theorem cls_frac_spacing {N : ℝ} (hN : 1 ≤ N) {ν : ℕ} (hν : 1 ≤ ν) {q q' : ℕ × ℕ}
    (hq : q ∈ cls N ν) (hq' : q' ∈ cls N ν) (hne : q ≠ q') :
    (ν : ℝ) ^ 2 / (4 * N ^ 2) ≤ |(q.2 : ℝ) / q.1 - (q'.2 : ℝ) / q'.1| := by
  obtain ⟨hq1, hq2, hg⟩ := mem_cls hq
  obtain ⟨hq1', hq2', hg'⟩ := mem_cls hq'
  obtain ⟨hn1, hn2⟩ := mem_closedRange_bounds hN hq1
  obtain ⟨hn1', hn2'⟩ := mem_closedRange_bounds hN hq1'
  have hn0 : 0 < q.1 := by exact_mod_cast (show (0 : ℝ) < q.1 by linarith)
  have hn0' : 0 < q'.1 := by exact_mod_cast (show (0 : ℝ) < q'.1 by linarith)
  have hn0R : (0 : ℝ) < q.1 := by linarith
  have hn0R' : (0 : ℝ) < q'.1 := by linarith
  have hfne : (q.2 : ℝ) / q.1 ≠ (q'.2 : ℝ) / q'.1 := by
    intro h
    apply hne
    rw [div_eq_div_iff hn0R.ne' hn0R'.ne'] at h
    have h' : q.2 * q'.1 = q'.2 * q.1 := by exact_mod_cast h
    obtain ⟨e1, e2⟩ := eq_of_cross_mul hν hn0 hg hg' h'
    exact Prod.ext e1 e2
  calc (ν : ℝ) ^ 2 / (4 * N ^ 2) ≤ (ν : ℝ) ^ 2 / ((q.1 : ℝ) * q'.1) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos hn0R hn0R')
        nlinarith
    _ ≤ _ := frac_spacing hn0 hn0' hg hg' hfne

/-- The number of `q ∈ cls N ν` with `|(q.2/q.1)^β − p| < Δ` is at most
`2Δ / (c(β) ν²/(4N²)) + 1`. -/
theorem card_cls_near_le {N : ℝ} (hN : 1 ≤ N) {ν : ℕ} (hν : 1 ≤ ν) {β : ℝ} (hβ : β ≠ 0)
    (p Δ : ℝ) (hΔ : 0 < Δ) :
    (((cls N ν).filter (fun q : ℕ × ℕ => |((q.2 : ℝ) / q.1) ^ β - p| < Δ)).card : ℝ) ≤
      2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))) + 1 := by
  classical
  set S := (cls N ν).filter (fun q : ℕ × ℕ => |((q.2 : ℝ) / q.1) ^ β - p| < Δ) with hS
  set φ : ℕ × ℕ → ℝ := fun q => ((q.2 : ℝ) / q.1) ^ β with hφ
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν
  have hδ : 0 < cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)) := mul_pos (cpow_pos hβ) (by positivity)
  have hsp : ∀ q ∈ cls N ν, ∀ q' ∈ cls N ν, q ≠ q' →
      cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)) ≤ |φ q - φ q'| := by
    intro q hq q' hq' hne
    obtain ⟨h1, h2, -⟩ := mem_cls hq
    obtain ⟨h1', h2', -⟩ := mem_cls hq'
    have hb := frac_bounds hN h1 h2
    have hb' := frac_bounds hN h1' h2'
    calc cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))
        ≤ cpow β * |(q.2 : ℝ) / q.1 - (q'.2 : ℝ) / q'.1| :=
          mul_le_mul_of_nonneg_left (cls_frac_spacing hN hν hq hq' hne) (cpow_pos hβ).le
      _ ≤ |((q.2 : ℝ) / q.1) ^ β - ((q'.2 : ℝ) / q'.1) ^ β| :=
          abs_rpow_sub_ge hb.1 hb.2 hb'.1 hb'.2
  have hinj : Set.InjOn φ S := by
    intro q hq q' hq' h
    replace hq : q ∈ S := hq
    replace hq' : q' ∈ S := hq'
    by_contra hne
    have := hsp q (Finset.mem_filter.1 hq).1 q' (Finset.mem_filter.1 hq').1 hne
    rw [h, sub_self, abs_zero] at this
    linarith
  have hY : ∀ y ∈ S.image φ, |y - p| < Δ := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact (Finset.mem_filter.1 hq).2
  have hsep : ∀ y ∈ S.image φ, ∀ y' ∈ S.image φ, y ≠ y' →
      cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)) ≤ |y - y'| := by
    intro y hy y' hy' hne
    rw [Finset.mem_image] at hy hy'
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨q', hq', rfl⟩ := hy'
    have hqne : q ≠ q' := fun h => hne (by rw [h])
    exact hsp q (Finset.mem_filter.1 hq).1 q' (Finset.mem_filter.1 hq').1 hqne
  calc (S.card : ℝ) = ((S.image φ).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ _ := card_le_of_spaced _ p Δ _ hδ hΔ hY hsep

theorem card_filter_product_eq {ι κ : Type*} (P : Finset ι) (Q : Finset κ) (R : ι × κ → Prop)
    [DecidablePred R] :
    ((P ×ˢ Q).filter R).card = ∑ p ∈ P, (Q.filter (fun q => R (p, q))).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

theorem card_filter_product_eq' {ι κ : Type*} (P : Finset ι) (Q : Finset κ) (R : ι × κ → Prop)
    [DecidablePred R] :
    ((P ×ˢ Q).filter R).card = ∑ q ∈ Q, (P.filter (fun p => R (p, q))).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  simp only [Finset.card_filter]

open Classical in
/-- The quadruples of the class `(μ, ν)`, as pairs of pairs. -/
noncomputable def clsPairs (α β M N Δ : ℝ) (μ ν : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (cls M μ ×ˢ cls N ν).filter fun pq =>
    |((pq.1.2 : ℝ) / pq.1.1) ^ α - ((pq.2.2 : ℝ) / pq.2.1) ^ β| < Δ

/-- Bound A: fix `(m, m̃)` and count `(n, ñ)`. -/
theorem card_clsPairs_le_A {α β M N Δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hΔ : 0 < Δ) (hβ : β ≠ 0)
    {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    ((clsPairs α β M N Δ μ ν).card : ℝ) ≤
      (2 * M / μ) ^ 2 * (1 + 2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)))) := by
  classical
  rw [clsPairs, card_filter_product_eq]
  push_cast
  have hterm : ∀ p ∈ cls M μ,
      (((cls N ν).filter fun q : ℕ × ℕ =>
        |((p.2 : ℝ) / p.1) ^ α - ((q.2 : ℝ) / q.1) ^ β| < Δ).card : ℝ) ≤
        2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))) + 1 := by
    intro p _
    refine le_trans ?_ (card_cls_near_le hN hν hβ (((p.2 : ℝ) / p.1) ^ α) Δ hΔ)
    exact_mod_cast Finset.card_le_card (fun q hq => by
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, by rw [abs_sub_comm]; exact hq.2⟩)
  calc _ ≤ ∑ p ∈ cls M μ, (2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))) + 1) :=
        Finset.sum_le_sum hterm
    _ = (cls M μ).card * (2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * M / μ) ^ 2 * (1 + 2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)))) := by
        rw [add_comm]
        exact mul_le_mul_of_nonneg_right (card_cls_le M hM μ hμ)
          (by linarith [show 0 ≤ 2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2))) from
            div_nonneg (by linarith) (mul_pos (cpow_pos hβ) (by positivity)).le])

/-- Bound B: fix `(n, ñ)` and count `(m, m̃)`. -/
theorem card_clsPairs_le_B {α β M N Δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hΔ : 0 < Δ) (hα : α ≠ 0)
    {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    ((clsPairs α β M N Δ μ ν).card : ℝ) ≤
      (2 * N / ν) ^ 2 * (1 + 2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2)))) := by
  classical
  rw [clsPairs, card_filter_product_eq']
  push_cast
  have hterm : ∀ q ∈ cls N ν,
      (((cls M μ).filter fun p : ℕ × ℕ =>
        |((p.2 : ℝ) / p.1) ^ α - ((q.2 : ℝ) / q.1) ^ β| < Δ).card : ℝ) ≤
        2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2))) + 1 := by
    intro q _
    exact card_cls_near_le hM hμ hα (((q.2 : ℝ) / q.1) ^ β) Δ hΔ
  calc _ ≤ ∑ q ∈ cls N ν, (2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2))) + 1) :=
        Finset.sum_le_sum hterm
    _ = (cls N ν).card * (2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2))) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * N / ν) ^ 2 * (1 + 2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2)))) := by
        rw [add_comm]
        exact mul_le_mul_of_nonneg_right (card_cls_le N hN ν hν)
          (by linarith [show 0 ≤ 2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2))) from
            div_nonneg (by linarith) (mul_pos (cpow_pos hα) (by positivity)).le])

/-- The class bound `≤ 4 min(M²/μ², N²/ν²) + (32 Δ M² N² / c) μ⁻² ν⁻²`. -/
theorem card_clsPairs_le {α β M N Δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hΔ : 0 < Δ) (hα : α ≠ 0)
    (hβ : β ≠ 0) {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    ((clsPairs α β M N Δ μ ν).card : ℝ) ≤
      4 * min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2) +
        32 * Δ * M ^ 2 * N ^ 2 / min (cpow α) (cpow β) * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) := by
  have hA := card_clsPairs_le_A (α := α) hM hN hΔ hβ hμ hν
  have hB := card_clsPairs_le_B (β := β) hM hN hΔ hα hμ hν
  have hμ0 : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν
  have hμne : (μ : ℝ) ≠ 0 := hμ0.ne'
  have hνne : (ν : ℝ) ≠ 0 := hν0.ne'
  have hMne : M ≠ 0 := by linarith
  have hNne : N ≠ 0 := by linarith
  have hcα := cpow_pos hα
  have hcβ := cpow_pos hβ
  have hcαne := hcα.ne'
  have hcβne := hcβ.ne'
  have hc : 0 < min (cpow α) (cpow β) := lt_min hcα hcβ
  have hnum : 0 ≤ 32 * Δ * M ^ 2 * N ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (sq_nonneg M)) (sq_nonneg N)
  have eA : (2 * M / μ) ^ 2 * (1 + 2 * Δ / (cpow β * ((ν : ℝ) ^ 2 / (4 * N ^ 2)))) =
      4 * (M ^ 2 / (μ : ℝ) ^ 2) +
        32 * Δ * M ^ 2 * N ^ 2 / cpow β * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) := by
    field_simp
    ring
  have eB : (2 * N / ν) ^ 2 * (1 + 2 * Δ / (cpow α * ((μ : ℝ) ^ 2 / (4 * M ^ 2)))) =
      4 * (N ^ 2 / (ν : ℝ) ^ 2) +
        32 * Δ * M ^ 2 * N ^ 2 / cpow α * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) := by
    field_simp
    ring
  have hZA : 32 * Δ * M ^ 2 * N ^ 2 / cpow β * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) ≤
      32 * Δ * M ^ 2 * N ^ 2 / min (cpow α) (cpow β) * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_left hnum hc (min_le_right _ _)
  have hZB : 32 * Δ * M ^ 2 * N ^ 2 / cpow α * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) ≤
      32 * Δ * M ^ 2 * N ^ 2 / min (cpow α) (cpow β) * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_left hnum hc (min_le_left _ _)
  rw [eA] at hA
  rw [eB] at hB
  rcases le_total (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-! ### Stage D: assembly -/

/-- The quadruple count is at most the sum of the class counts. -/
theorem quadrupleCount_le_sum {α β M N Δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    (quadrupleCount α β M N Δ : ℝ) ≤
      ∑ μ ∈ Finset.Icc 1 ⌊2 * M⌋₊, ∑ ν ∈ Finset.Icc 1 ⌊2 * N⌋₊,
        ((clsPairs α β M N Δ μ ν).card : ℝ) := by
  classical
  set Qd := ((closedRange M (2 * M) ×ˢ closedRange M (2 * M) ×ˢ
      closedRange N (2 * N) ×ˢ closedRange N (2 * N)).filter
    fun q : ℕ × ℕ × ℕ × ℕ =>
      |((q.2.1 : ℝ) / q.1) ^ α - ((q.2.2.2 : ℝ) / q.2.2.1) ^ β| < Δ) with hQd
  have hQ : quadrupleCount α β M N Δ = Qd.card := by
    unfold quadrupleCount
    rw [hQd]
  set g : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ :=
    fun q => (Nat.gcd q.1 q.2.1, Nat.gcd q.2.2.1 q.2.2.2) with hg
  have hM1 : 1 ≤ ⌈M⌉₊ := by rw [Nat.one_le_ceil_iff]; linarith
  have hN1 : 1 ≤ ⌈N⌉₊ := by rw [Nat.one_le_ceil_iff]; linarith
  have hmaps : (Qd : Set (ℕ × ℕ × ℕ × ℕ)).MapsTo g
      ((Finset.Icc 1 ⌊2 * M⌋₊ ×ˢ Finset.Icc 1 ⌊2 * N⌋₊ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro q hq
    replace hq : q ∈ Qd := hq
    rw [hQd, Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hq
    rw [closedRange, Finset.mem_Icc] at h1 h3
    show g q ∈ Finset.Icc 1 ⌊2 * M⌋₊ ×ˢ Finset.Icc 1 ⌊2 * N⌋₊
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc, hg]
    exact ⟨⟨Nat.gcd_pos_of_pos_left _ (by omega), le_trans (Nat.gcd_le_left _ (by omega)) h1.2⟩,
      ⟨Nat.gcd_pos_of_pos_left _ (by omega), le_trans (Nat.gcd_le_left _ (by omega)) h3.2⟩⟩
  rw [hQ, Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_product]
  push_cast
  refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => ?_
  have : (Qd.filter fun q => g q = (μ, ν)).card ≤ (clsPairs α β M N Δ μ ν).card := by
    refine Finset.card_le_card_of_injOn (fun q => ((q.1, q.2.1), (q.2.2.1, q.2.2.2))) ?_ ?_
    · intro q hq
      replace hq : q ∈ Qd.filter (fun q => g q = (μ, ν)) := hq
      rw [Finset.mem_filter, hQd, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product] at hq
      obtain ⟨⟨⟨h1, h2, h3, h4⟩, hcond⟩, hgq⟩ := hq
      rw [hg] at hgq
      simp only [Prod.mk.injEq] at hgq
      show ((q.1, q.2.1), (q.2.2.1, q.2.2.2)) ∈ clsPairs α β M N Δ μ ν
      rw [clsPairs, Finset.mem_filter, Finset.mem_product, cls, cls, Finset.mem_filter,
        Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨⟨⟨h1, h2⟩, hgq.1⟩, ⟨⟨h3, h4⟩, hgq.2⟩⟩, hcond⟩
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 (Prod.ext h.2.1 h.2.2))
  exact_mod_cast this

end FI

open FI in
/-- **Zhai–Cao, Lemma 6** (Fouvry–Iwaniec, Lemma 1) holds. -/
theorem zhaiCao_lemma6_holds : zhaiCao_lemma6 := by
  intro α β hαβ
  have hα : α ≠ 0 := left_ne_zero_of_mul hαβ
  have hβ : β ≠ 0 := right_ne_zero_of_mul hαβ
  have hc : 0 < min (cpow α) (cpow β) := lt_min (cpow_pos hα) (cpow_pos hβ)
  refine ⟨max 44 (288 / min (cpow α) (cpow β)), fun M N Δ hM hN hΔ => ?_⟩
  set U := ⌊2 * M⌋₊ with hU
  set V := ⌊2 * N⌋₊ with hV
  set c := min (cpow α) (cpow β) with hcdef
  set L := Real.log (2 * M * N) with hL
  have hU1 : (1 : ℝ) ≤ U := by
    rw [hU]
    exact_mod_cast Nat.le_floor (by norm_num; linarith : ((1 : ℕ) : ℝ) ≤ 2 * M)
  have hlogU : Real.log U ≤ L := by
    apply Real.log_le_log (by linarith)
    calc (U : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
      _ ≤ 2 * M * N := by nlinarith
  have hlog1 : 1 ≤ 7 / 4 * L := by
    have := BI.log_two_gt
    have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hsum := quadrupleCount_le_sum (α := α) (β := β) (Δ := Δ) hM hN
  have hmin := sum_sum_min_le U V M N (by linarith) (by linarith)
  have h3U := sum_inv_sq_le_three U
  have h3V := sum_inv_sq_le_three V
  have hnum : 0 ≤ 32 * Δ * M ^ 2 * N ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (sq_nonneg M)) (sq_nonneg N)
  have hZ0 : 0 ≤ 32 * Δ * M ^ 2 * N ^ 2 / c := div_nonneg hnum hc.le
  have hSig : ∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V, ((clsPairs α β M N Δ μ ν).card : ℝ) ≤
      ∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V,
        (4 * min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2) +
          32 * Δ * M ^ 2 * N ^ 2 / c * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2)) :=
    Finset.sum_le_sum fun μ hμ => Finset.sum_le_sum fun ν hν =>
      card_clsPairs_le hM hN hΔ hα hβ (Finset.mem_Icc.1 hμ).1 (Finset.mem_Icc.1 hν).1
  have hsplit : ∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V,
        (4 * min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2) +
          32 * Δ * M ^ 2 * N ^ 2 / c * (1 / (μ : ℝ) ^ 2) * (1 / (ν : ℝ) ^ 2)) =
      4 * (∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V,
          min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2)) +
        32 * Δ * M ^ 2 * N ^ 2 / c *
          ((∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) ^ 2) * (∑ ν ∈ Finset.Icc 1 V, 1 / (ν : ℝ) ^ 2)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  have hprod : (∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) ^ 2) * (∑ ν ∈ Finset.Icc 1 V, 1 / (ν : ℝ) ^ 2) ≤
      3 * 3 :=
    mul_le_mul h3U h3V (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
  have hA : 4 * (∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V,
      min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2)) ≤ 44 * (M * N * L) := by
    have h1 : 1 + Real.log U ≤ 11 / 4 * L := by linarith
    have hMN : 0 ≤ 16 * M * N := by positivity
    calc 4 * (∑ μ ∈ Finset.Icc 1 U, ∑ ν ∈ Finset.Icc 1 V,
          min (M ^ 2 / (μ : ℝ) ^ 2) (N ^ 2 / (ν : ℝ) ^ 2))
        ≤ 4 * (4 * M * N * (1 + Real.log U)) := by linarith
      _ = 16 * M * N * (1 + Real.log U) := by ring
      _ ≤ 16 * M * N * (11 / 4 * L) := mul_le_mul_of_nonneg_left h1 hMN
      _ = 44 * (M * N * L) := by ring
  have hB : 32 * Δ * M ^ 2 * N ^ 2 / c *
      ((∑ μ ∈ Finset.Icc 1 U, 1 / (μ : ℝ) ^ 2) * (∑ ν ∈ Finset.Icc 1 V, 1 / (ν : ℝ) ^ 2)) ≤
      288 / c * (Δ * M ^ 2 * N ^ 2) := by
    calc _ ≤ 32 * Δ * M ^ 2 * N ^ 2 / c * (3 * 3) := mul_le_mul_of_nonneg_left hprod hZ0
      _ = 288 / c * (Δ * M ^ 2 * N ^ 2) := by ring
  have hX0 : 0 ≤ M * N * L := by positivity
  have hY0 : 0 ≤ Δ * M ^ 2 * N ^ 2 := by positivity
  have hmax1 := mul_le_mul_of_nonneg_right (le_max_left 44 (288 / c)) hX0
  have hmax2 := mul_le_mul_of_nonneg_right (le_max_right 44 (288 / c)) hY0
  rw [mul_add]
  linarith


end LeanProofs.IntegerPoints
