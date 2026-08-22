import IntegerPoints.ExponentialSums

/-!
# The Weyl–van der Corput inequality (Zhai–Cao, Lemma 4)

A fully discrete proof of `zhaiCao_lemma4`.  For a finite block
`I = (A, B]` of integers, `h ≥ 1`, and `k ∈ ℕ`, let
`W_h(k) = ∑_{n ∈ I, k < n + h, n ≤ k} a_n` be the window sum of length `h`
ending at `k`.  Then

* `∑_k W_h(k) = h ∑_{n ∈ I} a_n`,
* `∑_k ‖W_h(k)‖² = ∑_{n, n' ∈ I} a_n \bar a_{n'} (h - |n - n'|)₊`,

and for real `Q = H + θ` (`H = ⌊Q⌋`, `0 ≤ θ < 1`) one has
`θ (H + 1 - d)₊ + (1 - θ)(H - d)₊ = (Q - d)₊` for every integer `d ≥ 0`.
Cauchy–Schwarz and convexity of the square then give
`Q² ‖∑ a_n‖² ≤ |K| ∑_{n,n'} ℜ(a_n \bar a_{n'}) (Q - |n - n'|)₊`
with `|K| = B - A + H + 1`, which is the inequality of Lemma 4 after
collecting the terms with `n' - n = q`.
-/

open Finset

namespace LeanProofs.IntegerPoints

namespace WeylVdC

variable (A B : ℕ) (a : ℕ → ℂ)

/-- The block `I = (A, B]`. -/
def I : Finset ℕ := Finset.Ioc A B

/-- The window sum of length `h` ending at `k`. -/
def W (h k : ℕ) : ℂ := ∑ n ∈ (I A B).filter (fun n => k < n + h ∧ n ≤ k), a n

/-- The range of window positions. -/
def Ks (h : ℕ) : Finset ℕ := Finset.Icc (A + 1) (B + h)

/-- `∑_k W_h(k) = h ∑_{n ∈ I} a_n`. -/
theorem sum_W (h : ℕ) : ∑ k ∈ Ks A B h, W A B a h k = (h : ℂ) * ∑ n ∈ I A B, a n := by
  unfold W
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← Finset.sum_filter]
  have hn' := Finset.mem_Ioc.1 hn
  have : (Ks A B h).filter (fun k => k < n + h ∧ n ≤ k) = Finset.Ico n (n + h) := by
    ext k
    simp only [Ks, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [this, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]

/-- The overlap count `(h - |n - n'|)₊`, as a natural number. -/
def overlap (h n n' : ℕ) : ℕ := min n n' + h - max n n'

/-- `W_h(k)` as a sum of indicators over `I`. -/
theorem W_eq (h k : ℕ) :
    W A B a h k = ∑ n ∈ I A B, if k < n + h ∧ n ≤ k then a n else 0 := by
  rw [W, Finset.sum_filter]

theorem conj_W_eq (h k : ℕ) :
    starRingEnd ℂ (W A B a h k) =
      ∑ n' ∈ I A B, if k < n' + h ∧ n' ≤ k then starRingEnd ℂ (a n') else 0 := by
  rw [W_eq, map_sum]
  refine Finset.sum_congr rfl fun n' _ => ?_
  split_ifs <;> simp

/-- `∑_k ‖W_h(k)‖² = ∑_{n, n'} a_n conj(a_{n'}) (h - |n - n'|)₊`. -/
theorem sum_normSq_W (h : ℕ) :
    ∑ k ∈ Ks A B h, (W A B a h k * starRingEnd ℂ (W A B a h k)) =
      ∑ n ∈ I A B, ∑ n' ∈ I A B, a n * starRingEnd ℂ (a n') * (overlap h n n' : ℂ) := by
  calc ∑ k ∈ Ks A B h, (W A B a h k * starRingEnd ℂ (W A B a h k))
      = ∑ k ∈ Ks A B h, ∑ n ∈ I A B, ∑ n' ∈ I A B,
          (if k < n + h ∧ n ≤ k then a n else 0) *
            (if k < n' + h ∧ n' ≤ k then starRingEnd ℂ (a n') else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [conj_W_eq, W_eq, Finset.sum_mul_sum]
    _ = ∑ n ∈ I A B, ∑ n' ∈ I A B, ∑ k ∈ Ks A B h,
          (if k < n + h ∧ n ≤ k then a n else 0) *
            (if k < n' + h ∧ n' ≤ k then starRingEnd ℂ (a n') else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ n ∈ I A B, ∑ n' ∈ I A B, a n * starRingEnd ℂ (a n') * (overlap h n n' : ℂ) := by
        refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun n' hn' => ?_
        have hn1 := Finset.mem_Ioc.1 hn
        have hn2 := Finset.mem_Ioc.1 hn'
        have key : ∀ k, (if k < n + h ∧ n ≤ k then a n else 0) *
            (if k < n' + h ∧ n' ≤ k then starRingEnd ℂ (a n') else 0) =
            if (k < n + h ∧ n ≤ k) ∧ (k < n' + h ∧ n' ≤ k) then
              a n * starRingEnd ℂ (a n') else 0 := by
          intro k
          split_ifs <;> simp_all
        simp_rw [key]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        have : (Ks A B h).filter (fun k => (k < n + h ∧ n ≤ k) ∧ (k < n' + h ∧ n' ≤ k)) =
            Finset.Ico (max n n') (min n n' + h) := by
          ext k
          simp only [Ks, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [this, Nat.card_Ico, overlap]

/-- Symmetric formulas for `overlap`. -/
theorem overlap_eq {h p q : ℕ} (hpq : p ≤ q) :
    overlap h p q = p + h - q ∧ overlap h q p = p + h - q := by
  unfold overlap
  rw [max_eq_right hpq, min_eq_left hpq, max_eq_left hpq, min_eq_right hpq]
  exact ⟨rfl, rfl⟩

/-- `θ (H + 1 - d)₊ + (1 - θ)(H - d)₊ = (Q - d)₊` for `Q = H + θ`, `0 ≤ θ < 1`. -/
theorem theta_overlap (Q : ℝ) (H : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hQ : Q = H + θ)
    (n n' : ℕ) :
    θ * (overlap (H + 1) n n' : ℝ) + (1 - θ) * (overlap H n n' : ℝ) =
      max 0 (Q - |(n : ℝ) - n'|) := by
  suffices key : ∀ p q : ℕ, p ≤ q →
      θ * ((p + (H + 1) - q : ℕ) : ℝ) + (1 - θ) * ((p + H - q : ℕ) : ℝ) =
        max 0 (Q - ((q : ℝ) - p)) by
    rcases le_total n n' with h | h
    · rw [(overlap_eq h).1, (overlap_eq h).1, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))]
      exact key n n' h
    · rw [(overlap_eq h).2, (overlap_eq h).2, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))]
      exact key n' n h
  intro p q hpq
  subst hQ
  rcases le_or_gt q (p + H) with hd | hd
  · have hd' : (q : ℝ) ≤ p + H := by exact_mod_cast hd
    rw [Nat.cast_sub (by omega), Nat.cast_sub hd]
    push_cast
    rw [max_eq_right (by linarith)]
    ring
  · have hd' : (p : ℝ) + H + 1 ≤ q := by exact_mod_cast hd
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)]
    push_cast
    rw [max_eq_left (by linarith)]
    ring

/-- Cauchy–Schwarz: `‖∑ f‖² ≤ |s| ∑ ‖f‖²`. -/
theorem norm_sum_sq_le (s : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ k ∈ s, f k‖ ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖f k‖ ^ 2 := by
  calc ‖∑ k ∈ s, f k‖ ^ 2 ≤ (∑ k ∈ s, ‖f k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ k ∈ s, 1 * ‖f k‖) ^ 2 := by simp
    _ ≤ (∑ k ∈ s, (1 : ℝ) ^ 2) * ∑ k ∈ s, ‖f k‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun k => ‖f k‖)
    _ = (s.card : ℝ) * ∑ k ∈ s, ‖f k‖ ^ 2 := by simp

/-- The real form of `sum_normSq_W`. -/
theorem sum_normSq_W_re (h : ℕ) :
    ∑ k ∈ Ks A B h, ‖W A B a h k‖ ^ 2 =
      ∑ n ∈ I A B, ∑ n' ∈ I A B, (a n * starRingEnd ℂ (a n')).re * (overlap h n n' : ℝ) := by
  calc ∑ k ∈ Ks A B h, ‖W A B a h k‖ ^ 2
      = (∑ k ∈ Ks A B h, W A B a h k * starRingEnd ℂ (W A B a h k)).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    _ = _ := by
        rw [sum_normSq_W, Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n' _ => ?_
        simp [Complex.mul_re]

/-- The core inequality:
`Q² ‖∑ a_n‖² ≤ (B - A + ⌊Q⌋ + 1) ∑_{n,n'} ℜ(a_n conj a_{n'}) (Q - |n - n'|)₊`. -/
theorem main (hAB : A ≤ B) (Q : ℝ) (hQ : 1 ≤ Q) :
    0 ≤ (∑ n ∈ I A B, ∑ n' ∈ I A B,
          (a n * starRingEnd ℂ (a n')).re * max 0 (Q - |(n : ℝ) - n'|)) ∧
    Q ^ 2 * ‖∑ n ∈ I A B, a n‖ ^ 2 ≤
      ((B : ℝ) - A + ⌊Q⌋₊ + 1) *
        ∑ n ∈ I A B, ∑ n' ∈ I A B,
          (a n * starRingEnd ℂ (a n')).re * max 0 (Q - |(n : ℝ) - n'|) := by
  have hH : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hH' : Q < ⌊Q⌋₊ + 1 := Nat.lt_floor_add_one Q
  generalize hHdef : ⌊Q⌋₊ = H at hH hH' ⊢
  set θ := Q - H with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  have hQθ : Q = H + θ := by rw [hθ]; ring
  set S := ∑ n ∈ I A B, a n with hS
  set X := ‖∑ k ∈ Ks A B (H + 1), W A B a (H + 1) k‖ with hX
  set Y := ‖∑ k ∈ Ks A B H, W A B a H k‖ with hY
  have hQS : (Q : ℂ) * S = (θ : ℂ) * ∑ k ∈ Ks A B (H + 1), W A B a (H + 1) k +
      ((1 - θ : ℝ) : ℂ) * ∑ k ∈ Ks A B H, W A B a H k := by
    rw [sum_W, sum_W, hθ]
    push_cast
    ring
  have h1 : Q * ‖S‖ ≤ θ * X + (1 - θ) * Y := by
    have : ‖(Q : ℂ) * S‖ = Q * ‖S‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [← this, hQS]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hθ0,
      Real.norm_of_nonneg (by linarith)]
  have h2 : (θ * X + (1 - θ) * Y) ^ 2 ≤ θ * X ^ 2 + (1 - θ) * Y ^ 2 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hθ1.le), sq_nonneg (X - Y)]
  have hcard : ∀ h, h ≤ H + 1 → ((Ks A B h).card : ℝ) ≤ (B : ℝ) - A + H + 1 := by
    intro h hh
    rw [Ks, Nat.card_Icc]
    have e : (B + h + 1 - (A + 1) : ℕ) = B + h - A := by omega
    rw [e, Nat.cast_sub (by omega)]
    push_cast
    have : (h : ℝ) ≤ H + 1 := by exact_mod_cast hh
    linarith
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hK : (0 : ℝ) ≤ (B : ℝ) - A + H + 1 := by linarith
  have hX2 : X ^ 2 ≤ ((B : ℝ) - A + H + 1) * ∑ k ∈ Ks A B (H + 1), ‖W A B a (H + 1) k‖ ^ 2 :=
    (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_right (hcard _ le_rfl)
      (Finset.sum_nonneg fun _ _ => by positivity))
  have hY2 : Y ^ 2 ≤ ((B : ℝ) - A + H + 1) * ∑ k ∈ Ks A B H, ‖W A B a H k‖ ^ 2 :=
    (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_right (hcard _ (Nat.le_succ _))
      (Finset.sum_nonneg fun _ _ => by positivity))
  have hmix : θ * ∑ k ∈ Ks A B (H + 1), ‖W A B a (H + 1) k‖ ^ 2 +
      (1 - θ) * ∑ k ∈ Ks A B H, ‖W A B a H k‖ ^ 2 =
      ∑ n ∈ I A B, ∑ n' ∈ I A B,
        (a n * starRingEnd ℂ (a n')).re * max 0 (Q - |(n : ℝ) - n'|) := by
    rw [sum_normSq_W_re, sum_normSq_W_re, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [← theta_overlap Q H θ hθ0 hθ1 hQθ n n']
    ring
  refine ⟨?_, ?_⟩
  · rw [← hmix]
    exact add_nonneg (mul_nonneg hθ0 (Finset.sum_nonneg fun _ _ => by positivity))
      (mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => by positivity))
  calc Q ^ 2 * ‖S‖ ^ 2 = (Q * ‖S‖) ^ 2 := by ring
    _ ≤ (θ * X + (1 - θ) * Y) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ θ * X ^ 2 + (1 - θ) * Y ^ 2 := h2
    _ ≤ θ * (((B : ℝ) - A + H + 1) * ∑ k ∈ Ks A B (H + 1), ‖W A B a (H + 1) k‖ ^ 2) +
          (1 - θ) * (((B : ℝ) - A + H + 1) * ∑ k ∈ Ks A B H, ‖W A B a H k‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hX2 hθ0)
          (mul_le_mul_of_nonneg_left hY2 (by linarith))
    _ = ((B : ℝ) - A + H + 1) *
          (θ * ∑ k ∈ Ks A B (H + 1), ‖W A B a (H + 1) k‖ ^ 2 +
            (1 - θ) * ∑ k ∈ Ks A B H, ‖W A B a H k‖ ^ 2) := by ring
    _ = _ := by rw [hmix]


/-- The inner sum of Lemma 4 at shift `q`: `ℜ ∑_{n, n+q ∈ I} a_n conj(a_{n+q})`. -/
def P (q : ℕ) : ℝ :=
  (∑ n ∈ (I A B).filter (fun n => n + q ∈ I A B), a n * starRingEnd ℂ (a (n + q))).re

/-- The summand of the double sum. -/
def F (Q : ℝ) (n n' : ℕ) : ℝ := (a n * starRingEnd ℂ (a n')).re * max 0 (Q - |(n : ℝ) - n'|)

theorem F_symm (Q : ℝ) (n n' : ℕ) : F a Q n n' = F a Q n' n := by
  unfold F
  rw [abs_sub_comm]
  congr 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Decomposition of the double sum into diagonal and twice the upper triangle. -/
theorem double_sum_decomp (Q : ℝ) :
    ∑ n ∈ I A B, ∑ n' ∈ I A B, F a Q n n' =
      ∑ n ∈ I A B, F a Q n n +
        2 * ∑ n ∈ I A B, ∑ n' ∈ (I A B).filter (fun n' => n < n'), F a Q n n' := by
  have hsplit : ∀ n ∈ I A B, ∑ n' ∈ I A B, F a Q n n' =
      F a Q n n + ∑ n' ∈ (I A B).filter (fun n' => n < n'), F a Q n n' +
        ∑ n' ∈ (I A B).filter (fun n' => n' < n), F a Q n n' := by
    intro n hn
    have h1 : (I A B).filter (fun n' => ¬ n < n' ∧ n' < n) =
        (I A B).filter (fun n' => n' < n) := Finset.filter_congr fun n' _ => by omega
    have h2 : (I A B).filter (fun n' => ¬ n < n' ∧ ¬ n' < n) = {n} := by
      ext n'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩
        omega
      · rintro rfl
        exact ⟨hn, by omega⟩
    rw [← Finset.sum_filter_add_sum_filter_not (I A B) (fun n' => n < n'),
      ← Finset.sum_filter_add_sum_filter_not ((I A B).filter (fun n' => ¬ n < n'))
        (fun n' => n' < n), Finset.filter_filter, Finset.filter_filter, h1, h2,
      Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hlower : ∑ n ∈ I A B, ∑ n' ∈ (I A B).filter (fun n' => n' < n), F a Q n n' =
      ∑ n ∈ I A B, ∑ n' ∈ (I A B).filter (fun n' => n < n'), F a Q n n' := by
    rw [Finset.sum_comm' (t' := I A B) (s' := fun n' => (I A B).filter (fun n => n' < n))]
    · refine Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun n _ => F_symm a Q n n'
    · intro n n'
      simp only [Finset.mem_filter]
      tauto
  rw [hlower]
  ring

/-- The upper triangle, reindexed by the shift `q = n' - n ∈ [1, H]`. -/
theorem upper_eq (Q : ℝ) (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ n' ∈ (I A B).filter (fun n' => n < n'), F a Q n n' =
      ∑ q ∈ (Finset.Ico 1 (⌊Q⌋₊ + 1)).filter (fun q => n + q ∈ I A B),
        (a n * starRingEnd ℂ (a (n + q))).re * (Q - q) := by
  have hH : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hH' : Q < ⌊Q⌋₊ + 1 := Nat.lt_floor_add_one Q
  -- terms with `n' > n + H` vanish
  have hsub : (I A B).filter (fun n' => n < n' ∧ n' ≤ n + ⌊Q⌋₊) ⊆
      (I A B).filter (fun n' => n < n') := by
    intro n' hn'
    simp only [Finset.mem_filter] at hn' ⊢
    exact ⟨hn'.1, hn'.2.1⟩
  have hzero : ∀ n' ∈ (I A B).filter (fun n' => n < n'),
      n' ∉ (I A B).filter (fun n' => n < n' ∧ n' ≤ n + ⌊Q⌋₊) → F a Q n n' = 0 := by
    intro n' hn' hn'2
    simp only [Finset.mem_filter, not_and, not_le] at hn' hn'2
    have hgt := hn'2 hn'.1 hn'.2
    unfold F
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 hn'.2.le))]
    have : (n : ℝ) + ⌊Q⌋₊ + 1 ≤ n' := by exact_mod_cast hgt
    rw [max_eq_left (by linarith), mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_nbij' (fun n' => n' - n) (fun q => n + q) ?_ ?_ ?_ ?_ ?_
  · intro n' hn'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn' ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_sub_cancel' hn'.2.1.le]
    exact hn'.1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    exact ⟨hq.2, by omega, by omega⟩
  · intro n' hn'
    simp only [Finset.mem_filter] at hn'
    omega
  · intro q _
    simp
  · intro n' hn'
    simp only [Finset.mem_filter] at hn'
    obtain ⟨-, hlt, hle⟩ := hn'
    unfold F
    rw [Nat.add_sub_cancel' hlt.le, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 hlt.le)), Nat.cast_sub hlt.le]
    congr 1
    have : ((n' : ℝ) - n) ≤ ⌊Q⌋₊ := by
      have := Nat.cast_le (α := ℝ) |>.2 hle
      push_cast at this
      linarith
    rw [max_eq_right (by linarith)]

/-- The double sum is at most twice the shifted-sum form of Lemma 4. -/
theorem double_sum_le (Q : ℝ) (hQ : 1 ≤ Q) :
    ∑ n ∈ I A B, ∑ n' ∈ I A B, F a Q n n' ≤
      2 * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), (Q - q) * P A B a q := by
  rw [double_sum_decomp]
  -- the diagonal is `Q * P 0`
  have hdiag : ∑ n ∈ I A B, F a Q n n = Q * P A B a 0 := by
    unfold P
    rw [Finset.filter_true_of_mem (fun n hn => by simpa using hn), Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold F
    simp only [sub_self, abs_zero, sub_zero, Nat.add_zero]
    rw [max_eq_right (by linarith)]
    ring
  have hP0 : 0 ≤ P A B a 0 := by
    unfold P
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun n _ => ?_
    rw [Nat.add_zero, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  -- the upper triangle is `∑_{q=1}^{H} (Q - q) P q`
  have hupper : ∑ n ∈ I A B, ∑ n' ∈ (I A B).filter (fun n' => n < n'), F a Q n n' =
      ∑ q ∈ Finset.Ico 1 (⌊Q⌋₊ + 1), (Q - q) * P A B a q := by
    rw [Finset.sum_congr rfl fun n _ => upper_eq A B a Q hQ n]
    rw [Finset.sum_comm' (t' := Finset.Ico 1 (⌊Q⌋₊ + 1))
      (s' := fun q => (I A B).filter (fun n => n + q ∈ I A B))]
    · refine Finset.sum_congr rfl fun q _ => ?_
      unfold P
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    · intro n q
      simp only [Finset.mem_filter]
      tauto
  rw [hdiag, hupper, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1)
    (by omega : 1 ≤ ⌊Q⌋₊ + 1)]
  rw [← Finset.range_eq_Ico, Finset.sum_range_one, Nat.cast_zero, sub_zero]
  have : 0 ≤ Q * P A B a 0 := mul_nonneg (by linarith) hP0
  linarith

end WeylVdC

/-- The inner range of Lemma 4 is the set of `n ∼ N` with `n + q ∼ N` as well. -/
theorem intRange_sub_eq_filter (N M : ℝ) (hM : 0 ≤ M) (q : ℕ) :
    intRange N (M - q) =
      (Finset.Ioc ⌊N⌋₊ ⌊M⌋₊).filter (fun n => n + q ∈ Finset.Ioc ⌊N⌋₊ ⌊M⌋₊) := by
  ext n
  simp only [intRange, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    have hn0 : n ≠ 0 := by omega
    rw [Nat.le_floor_iff' hn0] at h2
    have h3 : ((n + q : ℕ) : ℝ) ≤ M := by push_cast; linarith
    rw [← Nat.le_floor_iff hM] at h3
    exact ⟨⟨h1, by omega⟩, by omega, h3⟩
  · rintro ⟨⟨h1, -⟩, -, h3⟩
    have hn0 : n ≠ 0 := by omega
    refine ⟨h1, ?_⟩
    rw [Nat.le_floor_iff' hn0]
    rw [Nat.le_floor_iff hM] at h3
    push_cast at h3
    linarith

/-- **Zhai–Cao, Lemma 4** (Weyl–van der Corput), with `C = 6c`. -/
theorem zhaiCao_lemma4_holds : zhaiCao_lemma4 := by
  intro c hc
  refine ⟨6 * c, fun N Q a hQ hQN => ?_⟩
  have hN1 : 1 ≤ N := le_trans hQ hQN
  have hQ0 : 0 < Q := by linarith
  have hcN : N ≤ c * N := by nlinarith
  have hAB : ⌊N⌋₊ ≤ ⌊c * N⌋₊ := Nat.floor_le_floor hcN
  obtain ⟨hD0, hmain⟩ := WeylVdC.main ⌊N⌋₊ ⌊c * N⌋₊ a hAB Q hQ
  have hD := WeylVdC.double_sum_le ⌊N⌋₊ ⌊c * N⌋₊ a Q hQ
  have hS : intRange N (c * N) = WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊ := rfl
  have hPp : ∑ q ∈ Finset.range (⌊Q⌋₊ + 1),
      (1 - q / Q) * (∑ n ∈ intRange N (c * N - q), a n * starRingEnd ℂ (a (n + q))).re =
      (1 / Q) * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), (Q - q) * WeylVdC.P ⌊N⌋₊ ⌊c * N⌋₊ a q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [intRange_sub_eq_filter N (c * N) (by positivity) q]
    unfold WeylVdC.P WeylVdC.I
    field_simp
  set Pp := ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), (Q - q) * WeylVdC.P ⌊N⌋₊ ⌊c * N⌋₊ a q with hPpdef
  have hDF : ∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, ∑ n' ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊,
      (a n * starRingEnd ℂ (a n')).re * max 0 (Q - |(n : ℝ) - n'|) =
      ∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, ∑ n' ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊,
        WeylVdC.F a Q n n' := rfl
  rw [hDF] at hmain hD0
  have hPp0 : 0 ≤ Pp := by linarith
  set K : ℝ := (⌊c * N⌋₊ : ℝ) - ⌊N⌋₊ + ⌊Q⌋₊ + 1 with hK
  have hK0 : 0 ≤ K := by
    have : (⌊N⌋₊ : ℝ) ≤ ⌊c * N⌋₊ := by exact_mod_cast hAB
    rw [hK]
    linarith
  have hK2 : 2 * K ≤ 6 * c * N := by
    have h1 : (⌊c * N⌋₊ : ℝ) ≤ c * N := Nat.floor_le (by positivity)
    have h2 : N < ⌊N⌋₊ + 1 := Nat.lt_floor_add_one N
    have h3 : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0.le
    rw [hK]
    nlinarith
  rw [hS, hPp]
  have key : ‖∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, a n‖ ^ 2 * Q ^ 2 ≤
      (6 * c * (N / Q) * ((1 / Q) * Pp)) * Q ^ 2 := by
    calc ‖∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, a n‖ ^ 2 * Q ^ 2
        = Q ^ 2 * ‖∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, a n‖ ^ 2 := by ring
      _ ≤ K * ∑ n ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊, ∑ n' ∈ WeylVdC.I ⌊N⌋₊ ⌊c * N⌋₊,
            WeylVdC.F a Q n n' := hmain
      _ ≤ K * (2 * Pp) := mul_le_mul_of_nonneg_left hD hK0
      _ = (2 * K) * Pp := by ring
      _ ≤ (6 * c * N) * Pp := mul_le_mul_of_nonneg_right hK2 hPp0
      _ = (6 * c * (N / Q) * ((1 / Q) * Pp)) * Q ^ 2 := by
          field_simp
  exact le_of_mul_le_mul_right key (by positivity)

end LeanProofs.IntegerPoints
