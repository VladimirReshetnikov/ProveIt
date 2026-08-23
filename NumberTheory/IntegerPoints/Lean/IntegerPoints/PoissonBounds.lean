import IntegerPoints.Poisson

/-!
# Truncated Poisson summation: elementary bounds

Auxiliary facts for the proof of Graham–Kolesnik Lemma 3.5:

* periodicity of `ψ` and `S_N` under integer shifts and the uniform bound `|S_N| ≤ 4`;
* the Dirichlet kernel `K(x) = ∑_{H₁ ≤ h ≤ H₂} e(−hx)`: `‖K‖ ≤ H₂ − H₁ + 1` and
  `‖K(x)‖ ≤ 2/‖x‖`;
* the alternating-series bound `0 ≤ ∑_{k<n} (−1)^k u_k ≤ u_0` for antitone `u ≥ 0`;
* `∑_{k<n} 1/(k + 1 + u)² ≤ 2/(1 + u)`;
* `e(−h(m + 1/2)) = (−1)^h` for integers `h, m`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace PS

open Sawtooth EM SineIntegral

theorem norm_e_one (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-! ### Periodicity and the uniform bound on `S_N` -/

theorem S_add_int (N : ℕ) (x : ℝ) (m : ℤ) : S N (x + m) = S N x := by
  unfold S
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show 2 * π * (h + 1) * (x + m) = 2 * π * (h + 1) * x + (((h + 1 : ℕ) : ℤ) * m : ℤ) * (2 * π) by
    push_cast; ring, Real.sin_add_int_mul_two_pi]

theorem ψ_add_int (x : ℝ) (m : ℤ) : ψ (x + m) = ψ x := by
  unfold ψ
  rw [Int.fract_add_intCast]

theorem S_zero_apply (N : ℕ) : S N 0 = 0 := by
  unfold S
  simp

theorem abs_S_le_of_half {N : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : |S N x| ≤ 4 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [S]
  rcases eq_or_lt_of_le hx0 with hx0 | hx0
  · rw [← hx0, S_zero_apply, abs_zero]
    norm_num
  have hpi : 3 < π := BI.pi_gt_three'
  set u : ℝ := 2 * π * x with hu
  have hu0 : 0 < u := by positivity
  have huπ : u ≤ π := by rw [hu]; nlinarith
  rw [S_eq_integral, integral_D_eq N hu0 huπ]
  have hN1 : (1 : ℝ) ≤ N + 1 / 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1 := Perron.abs_s_le ((N + 1 / 2) * u)
  have hJ := integral_sin_mul_g_le (N := N + 1 / 2) hN1 hu0 huπ
  have hJ' : |∫ s in (0 : ℝ)..u, Real.sin ((N + 1 / 2) * s) * g s| ≤ 4 := by
    refine hJ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
    linarith
  set J := ∫ s in (0 : ℝ)..u, Real.sin ((N + 1 / 2) * s) * g s with hJdef
  have e1 : 1 / π * (Si ((N + 1 / 2) * u) - J) - x = Si ((N + 1 / 2) * u) / π - J / π - x := by
    ring
  rw [e1]
  have h2 : |J / π| ≤ 4 / 3 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith [abs_nonneg J]
  calc |Si ((N + 1 / 2) * u) / π - J / π - x|
      ≤ |Si ((N + 1 / 2) * u) / π - J / π| + |x| := abs_sub _ _
    _ ≤ (|Si ((N + 1 / 2) * u) / π| + |J / π|) + |x| := by gcongr; exact abs_sub _ _
    _ ≤ (3 / 2 + 4 / 3) + 1 / 2 := by
        gcongr
        rw [abs_of_pos hx0]; exact hx
    _ ≤ 4 := by norm_num

/-- The uniform bound `|S_N(x)| ≤ 4`. -/
theorem abs_S_le (N : ℕ) (x : ℝ) : |S N x| ≤ 4 := by
  have hx : S N x = S N (Int.fract x) := by
    conv_lhs => rw [← Int.fract_add_floor x]
    rw [S_add_int]
  rw [hx]
  set t := Int.fract x with ht
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  rcases le_or_gt t (1 / 2) with h | h
  · exact abs_S_le_of_half ht0 h
  · have : S N t = -S N (1 - t) := by
      rw [show (1 - t) = -t + 1 by ring, S_add_one, S_neg, neg_neg]
    rw [this, abs_neg]
    exact abs_S_le_of_half (by linarith) (by linarith)

/-- `|ψ(x) + S_N(x)| ≤ 9/2`. -/
theorem abs_ψ_add_S_le (N : ℕ) (x : ℝ) : |ψ x + S N x| ≤ 9 / 2 := by
  have h1 := abs_ψ_le x
  have h2 := abs_S_le N x
  calc |ψ x + S N x| ≤ |ψ x| + |S N x| := abs_add_le _ _
    _ ≤ 1 / 2 + 4 := add_le_add h1 h2
    _ = 9 / 2 := by norm_num

/-! ### Reindexing -/

theorem e_nat_mul (t : ℝ) (n : ℕ) : e (n * t) = e t ^ n := by
  induction n with
  | zero => simp [e]
  | succ n ih =>
    rw [pow_succ, ← ih, ← KL.e_add]
    congr 1
    push_cast
    ring

theorem sum_Icc_eq_sum_range (F : ℤ → ℂ) (H₁ : ℤ) (n : ℕ) :
    ∑ h ∈ Finset.Icc H₁ (H₁ + n), F h = ∑ j ∈ Finset.range (n + 1), F (H₁ + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Finset.Icc H₁ (H₁ + ((n + 1 : ℕ) : ℤ)) =
        insert (H₁ + (n : ℤ) + 1) (Finset.Icc H₁ (H₁ + n)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert (by simp), ih, Finset.sum_range_succ _ (n + 1)]
    push_cast
    rw [add_comm, show H₁ + ((n : ℤ) + 1) = H₁ + n + 1 by ring]

theorem sum_range_pair (I : ℤ → ℂ) (N : ℕ) :
    I 0 + ∑ k ∈ Finset.range N, (I (-((k : ℤ) + 1)) + I ((k : ℤ) + 1)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, I k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) (Finset.Icc (-(N : ℤ)) N)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    ring

/-- The symmetric range minus the middle range, for `N ≥ max(−H₁, H₂)`. -/
theorem Icc_sdiff_eq {H₁ H₂ : ℤ} {N : ℕ} (h1 : -(N : ℤ) ≤ H₁) (h2 : H₂ ≤ N) (h12 : H₁ ≤ H₂) :
    Finset.Icc (-(N : ℤ)) N \ Finset.Icc H₁ H₂ =
      Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union]
  omega

theorem disjoint_Icc_Icc {H₁ H₂ : ℤ} {N : ℕ} (h12 : H₁ ≤ H₂) :
    Disjoint (Finset.Icc (-(N : ℤ)) (H₁ - 1)) (Finset.Icc (H₂ + 1) N) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_Icc] at hx1 hx2
  omega

/-! ### The Dirichlet kernel -/

/-- `K(x) = ∑_{H₁ ≤ h ≤ H₂} e(−hx)`. -/
noncomputable def K (H₁ H₂ : ℤ) (x : ℝ) : ℂ := ∑ h ∈ Finset.Icc H₁ H₂, e (-(h * x))

theorem continuous_K (H₁ H₂ : ℤ) : Continuous (K H₁ H₂) := by
  unfold K
  apply continuous_finset_sum
  intro h _
  exact continuous_e_comp (by fun_prop)

theorem norm_K_le_card {H₁ H₂ : ℤ} (h12 : H₁ ≤ H₂) (x : ℝ) :
    ‖K H₁ H₂ x‖ ≤ (H₂ : ℝ) - H₁ + 1 := by
  unfold K
  calc ‖∑ h ∈ Finset.Icc H₁ H₂, e (-(h * x))‖ ≤ ∑ h ∈ Finset.Icc H₁ H₂, ‖e (-(h * x))‖ :=
        norm_sum_le _ _
    _ = ∑ h ∈ Finset.Icc H₁ H₂, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        exact norm_e_one _
    _ = (H₂ : ℝ) - H₁ + 1 := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
        have : (((H₂ + 1 - H₁).toNat : ℕ) : ℝ) = ((H₂ + 1 - H₁ : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega)
        rw [this]
        push_cast
        ring

theorem nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  unfold nearestIntDist
  exact abs_sub_round x

theorem nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := abs_nonneg _

/-- `‖K(x)‖ ≤ 2 / ‖x‖` when `x` is not an integer. -/
theorem norm_K_le_inv {H₁ H₂ : ℤ} (h12 : H₁ ≤ H₂) {x : ℝ} (hx : 0 < nearestIntDist x) :
    ‖K H₁ H₂ x‖ ≤ 2 / nearestIntDist x := by
  -- reindex
  obtain ⟨n, hn⟩ : ∃ n : ℕ, H₂ = H₁ + n := ⟨(H₂ - H₁).toNat, by omega⟩
  unfold K
  rw [hn, sum_Icc_eq_sum_range]
  -- `e(−(H₁ + j) x) = e(−H₁ x) e(−x)^j`
  have h1 : ∀ j : ℕ, e (-(((H₁ + j : ℤ) : ℝ) * x)) = e (-(H₁ * x)) * e (-x) ^ j := by
    intro j
    rw [← e_nat_mul, ← KL.e_add]
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, norm_mul, norm_e_one, one_mul]
  -- the geometric sum
  set g : ℝ := Int.fract (-x) with hg
  have hg0 : 0 ≤ g := Int.fract_nonneg _
  have hg1 : g < 1 := Int.fract_lt_one _
  have hgx : e g = e (-x) := by
    rw [hg, Int.fract, KL.e_sub_int]
  set lam := nearestIntDist x with hlam
  have hlam' : lam = nearestIntDist g := by
    rw [hlam, hg, Int.fract, KL.nearestIntDist_sub_int, KL.nearestIntDist_neg]
  have hlg1 : lam ≤ g := by
    rw [hlam']
    have := KL.nearestIntDist_le g 0
    simpa [abs_of_nonneg hg0] using this
  have hlg2 : g ≤ 1 - lam := by
    rw [hlam']
    have := KL.nearestIntDist_le g 1
    rw [Int.cast_one, abs_of_nonpos (by linarith)] at this
    linarith
  have hg0' : 0 < g := lt_of_lt_of_le hx hlg1
  have hlamh : lam ≤ 1 / 2 := hlam ▸ nearestIntDist_le_half x
  have hw := KL.e_sub_one_mul_w hg0' hg1
  have hne : e g - 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact zero_ne_one hw
  have hne' : e (-x) ≠ 1 := by
    rw [← hgx]
    intro h
    apply hne
    rw [h, sub_self]
  rw [geom_sum_eq hne', ← hgx]
  have hinv : (e g - 1)⁻¹ = KL.w g := by
    rw [← one_div, div_eq_iff hne]
    rw [mul_comm] at hw
    exact hw.symm
  rw [div_eq_mul_inv, hinv, norm_mul]
  have hwle := KL.norm_w_le hx hlamh hlg1 hlg2
  have hnum : ‖e g ^ (n + 1) - 1‖ ≤ 2 := by
    calc ‖e g ^ (n + 1) - 1‖ ≤ ‖e g ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, norm_e_one, one_pow, norm_one]
      _ = 2 := by norm_num
  calc ‖e g ^ (n + 1) - 1‖ * ‖KL.w g‖ ≤ 2 * (1 / lam) :=
        mul_le_mul hnum hwle (norm_nonneg _) (by norm_num)
    _ = 2 / lam := by ring

/-! ### The alternating-series bound -/

theorem alt_sum_bounds (u : ℕ → ℝ) (hu : Antitone u) (hu0 : ∀ n, 0 ≤ u n) :
    ∀ n m, 0 ≤ ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * u (m + k) ∧
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * u (m + k) ≤ u m := by
  intro n
  induction n with
  | zero => intro m; simp [hu0 m]
  | succ n ih =>
    intro m
    have h : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * u (m + k) =
        u m - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * u ((m + 1) + k) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, add_zero]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ, show m + (k + 1) = m + 1 + k by ring]
      ring
    rw [h]
    obtain ⟨h1, h2⟩ := ih (m + 1)
    have h3 : u (m + 1) ≤ u m := hu (Nat.le_succ m)
    constructor <;> linarith

/-- `|∑_{k<n} (−1)^k u_k| ≤ u_0` for antitone `u ≥ 0`. -/
theorem abs_alt_sum_le (u : ℕ → ℝ) (hu : Antitone u) (hu0 : ∀ n, 0 ≤ u n) (n : ℕ) :
    |∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * u k| ≤ u 0 := by
  have := alt_sum_bounds u hu hu0 n 0
  simp only [zero_add] at this
  rw [abs_le]
  constructor <;> linarith [hu0 0]

/-! ### `∑ 1/(k + 1 + u)²` -/

theorem sum_inv_sq_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 + u) ^ 2 ≤ 2 / (1 + u) := by
  have key : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1 + u) ^ 2 ≤
      2 / (1 + u) - 1 / ((n : ℝ) + 1 + u) := by
    intro n
    induction n with
    | zero =>
      have h0 : 0 < 1 + u := by linarith
      have e : (2 : ℝ) / (1 + u) - 1 / (((0 : ℕ) : ℝ) + 1 + u) = 1 / (1 + u) := by
        push_cast
        ring
      rw [e, Finset.sum_range_one]
      simp only [Nat.cast_zero, zero_add]
      rw [div_le_div_iff₀ (by positivity) h0]
      nlinarith
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : 1 / (((n + 1 : ℕ) : ℝ) + 1 + u) ^ 2 ≤
          1 / ((n : ℝ) + 1 + u) - 1 / (((n + 1 : ℕ) : ℝ) + 1 + u) := by
        push_cast
        have hp : 0 < (n : ℝ) + 1 + u := by positivity
        have hq : 0 < (n : ℝ) + 1 + 1 + u := by positivity
        rw [div_sub_div _ _ hp.ne' hq.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases n with _ | n
  · simp
    positivity
  · refine (key n).trans ?_
    have : 0 ≤ 1 / ((n : ℝ) + 1 + u) := by positivity
    linarith

/-! ### `e` at half-integers -/

theorem e_int_mul_half (h m : ℤ) : e (-((h : ℝ) * ((m : ℝ) + 1 / 2))) = (-1 : ℂ) ^ h := by
  have h1 : e (-((h : ℝ) * ((m : ℝ) + 1 / 2))) = e (((-h * m : ℤ) : ℝ)) * e (-(h : ℝ) / 2) := by
    rw [← KL.e_add]
    congr 1
    push_cast
    ring
  rw [h1, KL.e_int, one_mul]
  unfold e
  have h2 : (2 * π * Complex.I * ((-(h : ℝ) / 2 : ℝ) : ℂ) : ℂ) = ((-h : ℤ) : ℂ) * (π * Complex.I) := by
    push_cast
    ring
  rw [h2, Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_neg]
  rcases Int.even_or_odd h with he | ho
  · rw [he.neg_one_zpow, inv_one]
  · rw [ho.neg_one_zpow]
    norm_num

end PS

end LeanProofs.IntegerPoints
