import FabiusFunction.RogersSeries
import FabiusFunction.JacobiTripleProduct

/-!
# The Rogers–Ramanujan continued fraction: continuants and their limits

The finite truncations of `1 + q/(1 + q²/(1 + ⋯ + q^N/1))` are the rational continuants
`P_N/Q_N` with

  `P_0 = 1`, `P_1 = 1 + q`, `P_{N+2} = P_{N+1} + q^{N+2} P_N`,
  `Q_0 = 1`, `Q_1 = 1`,     `Q_{N+2} = Q_{N+1} + q^{N+2} Q_N`

(`continuantP`, `continuantQ`).  They are the Schur-type finitisations

  `P_N = ∑_j q^{j²} [N+1-j, j]_q`,  `Q_N = ∑_j q^{j²+j} [N-j, j]_q`

(`continuantP_eq_sum`, `continuantQ_eq_sum`, by the second `q`-Pascal rule), which converge to
the Rogers series `F_0 = G` and `F_1 = H` (`tendsto_continuantP`, `tendsto_continuantQ`, by
Tannery's theorem with the Gaussian majorant), so that

  `Q_N/P_N → H(q)/G(q) = (q, q⁴; q⁵)_∞ / (q², q³; q⁵)_∞`  (`tendsto_continuantQ_div_continuantP`,
  qg:thm-rrcf).
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

/-- The numerator continuants `P_N`. -/
def continuantP (q : R) : ℕ → R
  | 0 => 1
  | 1 => 1 + q
  | n + 2 => continuantP q (n + 1) + q ^ (n + 2) * continuantP q n

/-- The denominator continuants `Q_N`. -/
def continuantQ (q : R) : ℕ → R
  | 0 => 1
  | 1 => 1
  | n + 2 => continuantQ q (n + 1) + q ^ (n + 2) * continuantQ q n

/-- The Pascal step for the numerators: for `h ≤ N + 1`,
`q^{(h+1)²} [N+2-h, h+1] = q^{(h+1)²} [N+1-h, h+1] + q^{N+2} (q^{h²} [N+1-h, h])`. -/
theorem continuantP_step (q : R) {N h : ℕ} (hh : h ≤ N + 1) :
    q ^ ((h + 1) * (h + 1)) * gaussianBinomial q (N + 2 - h) (h + 1) =
      q ^ ((h + 1) * (h + 1)) * gaussianBinomial q (N + 1 - h) (h + 1) +
        q ^ (N + 2) * (q ^ (h * h) * gaussianBinomial q (N + 1 - h) h) := by
  rw [show N + 2 - h = (N + 1 - h) + 1 by omega, gaussianBinomial_succ_succ]
  rcases le_or_gt (2 * h) (N + 1) with h2 | h2
  · have e : (h + 1) * (h + 1) + (N + 1 - h - h) = N + 2 + h * h := by
      rw [show N + 1 - h - h = N + 1 - 2 * h by omega]
      zify [h2]
      ring
    rw [mul_add, ← mul_assoc, ← pow_add, e, pow_add]
    ring
  · rw [gaussianBinomial_eq_zero_of_lt q (show N + 1 - h < h by omega)]
    ring

/-- The Pascal step for the denominators: for `h ≤ N`,
`q^{(h+1)²+(h+1)} [N+1-h, h+1] = q^{(h+1)²+(h+1)} [N-h, h+1] + q^{N+2} (q^{h²+h} [N-h, h])`. -/
theorem continuantQ_step (q : R) {N h : ℕ} (hh : h ≤ N) :
    q ^ ((h + 1) * (h + 1) + (h + 1)) * gaussianBinomial q (N + 1 - h) (h + 1) =
      q ^ ((h + 1) * (h + 1) + (h + 1)) * gaussianBinomial q (N - h) (h + 1) +
        q ^ (N + 2) * (q ^ (h * h + h) * gaussianBinomial q (N - h) h) := by
  rw [show N + 1 - h = (N - h) + 1 by omega, gaussianBinomial_succ_succ]
  rcases le_or_gt (2 * h) N with h2 | h2
  · have e : (h + 1) * (h + 1) + (h + 1) + (N - h - h) = N + 2 + (h * h + h) := by
      rw [show N - h - h = N - 2 * h by omega]
      zify [h2]
      ring
    rw [mul_add, ← mul_assoc, ← pow_add, e, pow_add]
    ring
  · rw [gaussianBinomial_eq_zero_of_lt q (show N - h < h by omega)]
    ring

/-- `P_N = ∑_{j ≤ N+1} q^{j²} [N+1-j, j]_q`. -/
theorem continuantP_eq_sum (q : R) (N : ℕ) :
    continuantP q N = ∑ j ∈ range (N + 2), q ^ (j * j) * gaussianBinomial q (N + 1 - j) j := by
  have key : ∀ N, continuantP q N =
        (∑ j ∈ range (N + 2), q ^ (j * j) * gaussianBinomial q (N + 1 - j) j) ∧
      continuantP q (N + 1) =
        ∑ j ∈ range (N + 1 + 2), q ^ (j * j) * gaussianBinomial q (N + 1 + 1 - j) j := by
    intro N
    induction N with
    | zero =>
        constructor
        · simp [continuantP, sum_range_succ]
        · simp [continuantP, sum_range_succ]
    | succ N ih =>
        refine ⟨ih.2, ?_⟩
        rw [continuantP, ih.2, ih.1]
        rw [sum_range_succ' (fun j => q ^ (j * j) * gaussianBinomial q (N + 1 + 1 + 1 - j) j),
          sum_range_succ (fun h => q ^ ((h + 1) * (h + 1)) *
            gaussianBinomial q (N + 1 + 1 + 1 - (h + 1)) (h + 1)),
          sum_range_succ' (fun j => q ^ (j * j) * gaussianBinomial q (N + 1 + 1 - j) j), mul_sum,
          gaussianBinomial_eq_zero_of_lt q (show N + 1 + 1 + 1 - (N + 2 + 1) < N + 2 + 1 by omega)]
        simp only [mul_zero, add_zero, pow_zero, Nat.sub_zero, gaussianBinomial_zero_right, mul_one]
        rw [add_right_comm, ← sum_add_distrib]
        congr 1
        refine sum_congr rfl fun h hh => ?_
        have hh' : h ≤ N + 1 := Nat.lt_succ_iff.mp (mem_range.mp hh)
        have := continuantP_step q (N := N) hh'
        rw [show N + 1 + 1 + 1 - (h + 1) = N + 2 - h by omega,
          show N + 1 + 1 - (h + 1) = N + 1 - h by omega]
        exact this.symm
  exact (key N).1

/-- `Q_N = ∑_{j ≤ N} q^{j²+j} [N-j, j]_q`. -/
theorem continuantQ_eq_sum (q : R) (N : ℕ) :
    continuantQ q N = ∑ j ∈ range (N + 1), q ^ (j * j + j) * gaussianBinomial q (N - j) j := by
  have key : ∀ N, continuantQ q N =
        (∑ j ∈ range (N + 1), q ^ (j * j + j) * gaussianBinomial q (N - j) j) ∧
      continuantQ q (N + 1) =
        ∑ j ∈ range (N + 1 + 1), q ^ (j * j + j) * gaussianBinomial q (N + 1 - j) j := by
    intro N
    induction N with
    | zero =>
        constructor
        · simp [continuantQ]
        · simp [continuantQ, sum_range_succ]
    | succ N ih =>
        refine ⟨ih.2, ?_⟩
        rw [continuantQ, ih.2, ih.1]
        rw [sum_range_succ' (fun j => q ^ (j * j + j) * gaussianBinomial q (N + 1 + 1 - j) j),
          sum_range_succ (fun h => q ^ ((h + 1) * (h + 1) + (h + 1)) *
            gaussianBinomial q (N + 1 + 1 - (h + 1)) (h + 1)),
          sum_range_succ' (fun j => q ^ (j * j + j) * gaussianBinomial q (N + 1 - j) j), mul_sum,
          gaussianBinomial_eq_zero_of_lt q (show N + 1 + 1 - (N + 1 + 1) < N + 1 + 1 by omega)]
        simp only [mul_zero, add_zero, pow_zero, Nat.sub_zero, gaussianBinomial_zero_right, mul_one]
        rw [add_right_comm, ← sum_add_distrib]
        congr 1
        refine sum_congr rfl fun h hh => ?_
        have hh' : h ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hh)
        have := continuantQ_step q (N := N) hh'
        rw [show N + 1 + 1 - (h + 1) = N + 1 - h by omega,
          show N + 1 - (h + 1) = N - h by omega]
        exact this.symm
  exact (key N).1

end CommRing

section Limits

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `P_N → F_0(q) = G(q)`. -/
theorem tendsto_continuantP {q : 𝕜} (hq : ‖q‖ < 1) :
    Tendsto (fun N => continuantP q N) atTop (𝓝 (rogersSeries q 0)) := by
  set M := gaussianMajorant q with hM
  have hM0 : 0 ≤ M := gaussianMajorant_nonneg hq
  let f : ℕ → ℕ → 𝕜 := fun N j =>
    if j ≤ N + 1 then q ^ (j * j) * gaussianBinomial q (N + 1 - j) j else 0
  have hfin : ∀ N, ∑' j, f N j = continuantP q N := by
    intro N
    rw [tsum_eq_sum (s := range (N + 2)) (fun j hj => by
      simp only [f]
      rw [mem_range] at hj
      rw [if_neg (by omega)]), continuantP_eq_sum]
    refine sum_congr rfl fun j hj => ?_
    simp only [f]
    rw [if_pos (by have := mem_range.mp hj; omega)]
  have hbound : Summable fun j : ℕ => ‖q‖ ^ (j * j) * M := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right M)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self j)) hM0
  have hb : ∀ N j, ‖f N j‖ ≤ ‖q‖ ^ (j * j) * M := by
    intro N j
    simp only [f]
    split_ifs
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_gaussianBinomial_le hq _ _) (by positivity)
    · rw [norm_zero]
      positivity
  have hpt : ∀ j, Tendsto (fun N => f N j) atTop
      (𝓝 (q ^ (j * j) * (finiteQPochhammerIn q q j)⁻¹)) := by
    intro j
    have h1 : Tendsto (fun N : ℕ => N + 1 - j) atTop atTop :=
      (tendsto_sub_atTop_nat j).comp (tendsto_add_atTop_nat 1)
    have h2 := ((tendsto_gaussianBinomial_atTop hq j).comp h1).const_mul (q ^ (j * j))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp only [f, Function.comp]
    rw [if_pos (by omega)]
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpt (Eventually.of_forall hb)
  simp only [hfin] at hlim
  have heq : ∑' j, q ^ (j * j) * (finiteQPochhammerIn q q j)⁻¹ = rogersSeries q 0 := by
    unfold rogersSeries
    refine tsum_congr fun j => ?_
    rw [Nat.zero_mul, Nat.add_zero, div_eq_mul_inv]
  rw [heq] at hlim
  exact hlim

/-- `Q_N → F_1(q) = H(q)`. -/
theorem tendsto_continuantQ {q : 𝕜} (hq : ‖q‖ < 1) :
    Tendsto (fun N => continuantQ q N) atTop (𝓝 (rogersSeries q 1)) := by
  set M := gaussianMajorant q with hM
  have hM0 : 0 ≤ M := gaussianMajorant_nonneg hq
  let f : ℕ → ℕ → 𝕜 := fun N j =>
    if j ≤ N then q ^ (j * j + j) * gaussianBinomial q (N - j) j else 0
  have hfin : ∀ N, ∑' j, f N j = continuantQ q N := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1)) (fun j hj => by
      simp only [f]
      rw [mem_range] at hj
      rw [if_neg (by omega)]), continuantQ_eq_sum]
    refine sum_congr rfl fun j hj => ?_
    simp only [f]
    rw [if_pos (by have := mem_range.mp hj; omega)]
  have hbound : Summable fun j : ℕ => ‖q‖ ^ (j * j + j) * M := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right M)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith [Nat.le_mul_self j])) hM0
  have hb : ∀ N j, ‖f N j‖ ≤ ‖q‖ ^ (j * j + j) * M := by
    intro N j
    simp only [f]
    split_ifs
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_gaussianBinomial_le hq _ _) (by positivity)
    · rw [norm_zero]
      positivity
  have hpt : ∀ j, Tendsto (fun N => f N j) atTop
      (𝓝 (q ^ (j * j + j) * (finiteQPochhammerIn q q j)⁻¹)) := by
    intro j
    have h2 := ((tendsto_gaussianBinomial_atTop hq j).comp (tendsto_sub_atTop_nat j)).const_mul
      (q ^ (j * j + j))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp only [f, Function.comp]
    rw [if_pos hN]
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpt (Eventually.of_forall hb)
  simp only [hfin] at hlim
  have heq : ∑' j, q ^ (j * j + j) * (finiteQPochhammerIn q q j)⁻¹ = rogersSeries q 1 := by
    unfold rogersSeries
    refine tsum_congr fun j => ?_
    rw [Nat.one_mul, div_eq_mul_inv]
  rw [heq] at hlim
  exact hlim

/-- **The Rogers–Ramanujan continued fraction** (qg:thm-rrcf, the convergence of the rational
continuants): `Q_N/P_N → H(q)/G(q) = (q, q⁴; q⁵)_∞ / (q², q³; q⁵)_∞`. -/
theorem tendsto_continuantQ_div_continuantP {q : 𝕜} (hq : ‖q‖ < 1) :
    Tendsto (fun N => continuantQ q N / continuantP q N) atTop
      (𝓝 (qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5) /
        (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5)))) := by
  have h0 : rogersSeries q 0 ≠ 0 := by
    rw [rogersSeries_zero_eq hq]
    exact inv_ne_zero (mul_ne_zero (qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_five_lt_one hq) hq)
      (qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 4) (by norm_num)))
  have h := (tendsto_continuantQ hq).div (tendsto_continuantP hq) h0
  rw [rogersSeries_zero_eq hq, rogersSeries_one_eq hq] at h
  have h2 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 2) (by norm_num)
  have h3 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 3) (by norm_num)
  have h1 := qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_five_lt_one hq) hq
  have h4 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 4) (by norm_num)
  rw [show (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹ /
      (qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹ =
      qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5) /
        (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5)) by
    rw [div_eq_mul_inv, inv_inv, mul_comm, div_eq_mul_inv]] at h
  exact h

end Limits

end Fabius
