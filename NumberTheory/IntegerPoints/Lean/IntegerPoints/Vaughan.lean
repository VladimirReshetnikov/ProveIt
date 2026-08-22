import IntegerPoints.Wu

/-!
# The Vaughan identity for `μ` (Wu, Lemma 4.1 / (4.1))

We prove `wu_vaughanIdentity_pointwise` by Dirichlet convolution.  Let
`T = μ · 1_{≤U}` be the truncated Möbius function.  Then `b = T * ζ`,
`a = T * T`, and for `U ≥ 1` the restriction of `b` to `k > U` is
`T * ζ - 1`.  Hence the second sum of the identity is
`((μ - T) * (T ζ - 1))(n) = (T (μ ζ) - T² ζ - μ + T)(n)`, and `T(n) = 0`
for `n > U`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace LeanProofs.IntegerPoints

/-- `(f - g) n = f n - g n` for arithmetic functions. -/
theorem ArithmeticFunction.sub_apply' {R : Type*} [AddGroup R]
    {f g : ArithmeticFunction R} {n : ℕ} : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, sub_eq_add_neg]

open Classical in
/-- The truncated Möbius function `T(d) = μ(d) 1_{d ≤ U}`. -/
noncomputable def moebiusTrunc (U : ℝ) : ArithmeticFunction ℤ :=
  ⟨fun d => if (d : ℝ) ≤ U then μ d else 0, by simp⟩

open Classical in
theorem moebiusTrunc_apply (U : ℝ) (d : ℕ) :
    moebiusTrunc U d = if (d : ℝ) ≤ U then μ d else 0 := rfl

/-- `b = T * ζ`. -/
theorem vaughanB_eq (U : ℝ) (k : ℕ) : vaughanB U k = (moebiusTrunc U * ζ) k := by
  classical
  rw [coe_mul_zeta_apply, vaughanB, Finset.sum_filter]
  rfl

/-- `a = T * T`. -/
theorem vaughanA_eq (U : ℝ) (j : ℕ) :
    vaughanA U j = (moebiusTrunc U * moebiusTrunc U) j := by
  classical
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => moebiusTrunc U a * moebiusTrunc U b),
    vaughanA, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [moebiusTrunc_apply]
  by_cases h1 : (d : ℝ) ≤ U <;> by_cases h2 : ((j / d : ℕ) : ℝ) ≤ U <;> simp [h1, h2]

/-- `∑_{j ∣ n, j ≤ U²} a_j = (T * T * ζ)(n)`; the restriction `j ≤ U²` is
automatic. -/
theorem sum_vaughanA (U : ℝ) (hU : 0 ≤ U) (n : ℕ) :
    ∑ j ∈ n.divisors.filter (fun j : ℕ => (j : ℝ) ≤ U ^ 2), vaughanA U j =
      (moebiusTrunc U * moebiusTrunc U * ζ) n := by
  classical
  rw [coe_mul_zeta_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← vaughanA_eq]
  split_ifs with h
  · rfl
  symm
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply h
  have hjd : j = d * (j / d) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd.1)).symm
  have hj' : (j : ℝ) = (d : ℝ) * ((j / d : ℕ) : ℝ) := by exact_mod_cast hjd
  rw [hj', pow_two]
  exact mul_le_mul hd.2.1 hd.2.2 (by positivity) hU

open Classical in
/-- The restriction of `b` to `k > U`. -/
noncomputable def vaughanBHi (U : ℝ) : ArithmeticFunction ℤ :=
  ⟨fun k => if U < (k : ℝ) then vaughanB U k else 0, by simp [vaughanB]⟩

open Classical in
theorem vaughanBHi_apply (U : ℝ) (k : ℕ) :
    vaughanBHi U k = if U < (k : ℝ) then vaughanB U k else 0 := rfl

/-- The second sum of the identity is `((μ - T) * b_{>U})(n)`. -/
theorem sum_vaughan_hi (U : ℝ) (n : ℕ) :
    ∑ j ∈ n.divisors.filter (fun j : ℕ => U < (j : ℝ) ∧ U < ((n / j : ℕ) : ℝ)),
        μ j * vaughanB U (n / j) =
      ((μ - moebiusTrunc U) * vaughanBHi U) n := by
  classical
  rw [mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (μ - moebiusTrunc U) a * vaughanBHi U b),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ArithmeticFunction.sub_apply', moebiusTrunc_apply, vaughanBHi_apply]
  by_cases h1 : U < (j : ℝ)
  · have h1' : ¬ ((j : ℝ) ≤ U) := not_le.2 h1
    by_cases h2 : U < ((n / j : ℕ) : ℝ) <;> simp [h1, h1', h2]
  · have h1' : (j : ℝ) ≤ U := not_lt.1 h1
    by_cases h2 : U < ((n / j : ℕ) : ℝ) <;> simp [h1, h1', h2]

/-- For `U ≥ 1`, `b_{>U} = T * ζ - 1`. -/
theorem vaughanBHi_eq (U : ℝ) (hU : 1 ≤ U) : vaughanBHi U = moebiusTrunc U * ζ - 1 := by
  classical
  refine ArithmeticFunction.ext fun k => ?_
  rw [vaughanBHi_apply, ArithmeticFunction.sub_apply', ← vaughanB_eq, one_apply]
  by_cases h1 : U < (k : ℝ)
  · have hk : k ≠ 1 := by
      rintro rfl
      simp at h1
      linarith
    rw [if_pos h1, if_neg hk]
    ring
  · rw [not_lt] at h1
    rw [if_neg (not_lt.2 h1), vaughanB, Finset.filter_true_of_mem, ← coe_mul_zeta_apply,
      moebius_mul_coe_zeta, one_apply]
    · ring
    intro d hd
    exact le_trans (by exact_mod_cast Nat.divisor_le hd) h1

/-- **Vaughan's identity for `μ`** (`wu_vaughanIdentity_pointwise`). -/
theorem wu_vaughanIdentity_pointwise_holds : wu_vaughanIdentity_pointwise := by
  classical
  intro U n hU hn
  rw [sum_vaughanA U (by linarith) n, sum_vaughan_hi U n, vaughanBHi_eq U hU]
  set T := moebiusTrunc U with hT
  have hTn : T n = 0 := by
    rw [hT, moebiusTrunc_apply, if_neg (not_le.2 hn)]
  have key : (μ - T) * (T * ζ - 1) = T * (μ * ζ) - T * T * ζ - μ + T := by ring
  rw [key, moebius_mul_coe_zeta, mul_one, ArithmeticFunction.add_apply,
    ArithmeticFunction.sub_apply', ArithmeticFunction.sub_apply', hTn]
  ring

/-! ### The summed form (4.1) -/

/-- `k ∈ dyadic (N / j) ↔ j k ∈ dyadic N` for `j > 0` and `N ≥ 0`. -/
theorem mem_dyadic_div_iff {N : ℝ} (hN : 0 ≤ N) {j k : ℕ} (hj : 0 < j) :
    k ∈ dyadic (N / j) ↔ j * k ∈ dyadic N := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  simp only [dyadic, intRange, Finset.mem_Ioc]
  rw [← mul_div_assoc, Nat.floor_lt (div_nonneg hN hj'.le),
    Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * N / j), Nat.floor_lt hN,
    Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * N), Nat.cast_mul,
    div_lt_iff₀ hj', le_div_iff₀ hj', mul_comm (k : ℝ) j]

/-- For `j > 0`, the block `k ∼ N / j` is the set of `k ≤ 2N` with `jk ∼ N`. -/
theorem dyadic_div_eq_filter {N : ℝ} (hN : 0 ≤ N) {j : ℕ} (hj : 0 < j) :
    dyadic (N / j) = (upTo (2 * N)).filter (fun k => j * k ∈ dyadic N) := by
  ext k
  rw [Finset.mem_filter, mem_dyadic_div_iff hN hj, upTo, Finset.mem_Icc]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · simp only [dyadic, intRange, Finset.mem_Ioc] at h
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp at h
      · exact hk
    · simp only [dyadic, intRange, Finset.mem_Ioc] at h
      exact le_trans (Nat.le_mul_of_pos_left k hj) h.2
  · exact fun h => h.2

/-- Reindexing `(j, k) ↦ (n, j)` with `n = j k`: a double sum over pairs with
`jk ∼ N` equals a sum over `n ∼ N` and divisors `j ∣ n`. -/
theorem sum_pairs_eq_sum_dyadic {β : Type*} [AddCommMonoid β] (N : ℝ)
    (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j) (P : ℕ → ℕ → Prop) [∀ j k, Decidable (P j k)]
    (g : ℕ → ℕ → β) :
    ∑ j ∈ s, ∑ k ∈ (upTo (2 * N)).filter (fun k => j * k ∈ dyadic N ∧ P j k), g j k =
      ∑ n ∈ dyadic N, ∑ j ∈ n.divisors.filter (fun j => j ∈ s ∧ P j (n / j)), g j (n / j) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.1 * x.2, x.1⟩) (fun y _ => ⟨y.2, y.1 / y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, upTo, Finset.mem_Icc] at hx
    obtain ⟨hj, ⟨hk1, hk2⟩, hjk, hP⟩ := hx
    have hj0 := hs j hj
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨hjk, ⟨dvd_mul_right j k, by positivity⟩, hj, ?_⟩
    rwa [Nat.mul_div_cancel_left k hj0]
  · rintro ⟨n, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hy
    obtain ⟨hn, ⟨hjn, hn0⟩, hj, hP⟩ := hy
    have hj0 := hs j hj
    simp only [Finset.mem_sigma, Finset.mem_filter, upTo, Finset.mem_Icc]
    rw [Nat.mul_div_cancel' hjn]
    refine ⟨hj, ⟨?_, ?_⟩, hn, hP⟩
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hjn) hj0
    · simp only [dyadic, intRange, Finset.mem_Ioc] at hn
      exact le_trans (Nat.div_le_self n j) hn.2
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx
    have hj0 := hs j hx.1
    simp only [Nat.mul_div_cancel_left k hj0]
  · rintro ⟨n, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hy
    simp only [Nat.mul_div_cancel' hy.2.1.1]
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx
    have hj0 := hs j hx.1
    simp only [Nat.mul_div_cancel_left k hj0]

/-- Elements of `dyadic N` are positive and at most `⌊2N⌋₊`. -/
theorem mem_dyadic_bounds {N : ℝ} {n : ℕ} (hn : n ∈ dyadic N) : 0 < n ∧ n ≤ ⌊2 * N⌋₊ := by
  simp only [dyadic, intRange, Finset.mem_Ioc] at hn
  exact ⟨lt_of_le_of_lt (Nat.zero_le _) hn.1, hn.2⟩

/-- **Wu, (4.1)** (`wu_vaughanIdentity`), the summed Vaughan identity. -/
theorem wu_vaughanIdentity_holds : wu_vaughanIdentity := by
  classical
  intro U N f hU hUN
  have hN : 0 ≤ N := by linarith
  -- the first double sum
  have h1 : ∑ j ∈ upTo (U ^ 2), ∑ k ∈ dyadic (N / j), (vaughanA U j : ℂ) * f (j * k) =
      ∑ n ∈ dyadic N,
        (∑ j ∈ n.divisors.filter (fun j : ℕ => (j : ℝ) ≤ U ^ 2), (vaughanA U j : ℂ)) * f n := by
    have hpos : ∀ j ∈ upTo (U ^ 2), 0 < j := fun j hj =>
      lt_of_lt_of_le one_pos (Finset.mem_Icc.1 hj).1
    rw [Finset.sum_congr rfl (fun j hj => by rw [dyadic_div_eq_filter hN (hpos j hj)])]
    have := sum_pairs_eq_sum_dyadic N (upTo (U ^ 2)) hpos (fun _ _ => True)
      (fun j k => (vaughanA U j : ℂ) * f (j * k))
    simp only [and_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr ?_ fun j hj => ?_
    · apply Finset.filter_congr
      intro j hj
      have hj0 := Nat.pos_of_mem_divisors hj
      rw [upTo, Finset.mem_Icc, Nat.le_floor_iff (by positivity)]
      exact ⟨fun h => h.2, fun h => ⟨hj0, h⟩⟩
    · rw [Finset.mem_filter] at hj
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hj.1)]
  -- the second double sum
  have hfilt : ∀ j : ℕ, (upTo (2 * N)).filter
        (fun k : ℕ => U < (j : ℝ) ∧ U < (k : ℝ) ∧ j * k ∈ dyadic N) =
      (upTo (2 * N)).filter (fun k : ℕ => j * k ∈ dyadic N ∧ U < (j : ℝ) ∧ U < (k : ℝ)) :=
    fun j => Finset.filter_congr (fun k _ => by tauto)
  have h2 : ∑ j ∈ upTo (2 * N), ∑ k ∈ (upTo (2 * N)).filter
        (fun k : ℕ => j * k ∈ dyadic N ∧ U < (j : ℝ) ∧ U < (k : ℝ)),
        moebiusC j * (vaughanB U k : ℂ) * f (j * k) =
      ∑ n ∈ dyadic N,
        (∑ j ∈ n.divisors.filter (fun j : ℕ => U < (j : ℝ) ∧ U < ((n / j : ℕ) : ℝ)),
          moebiusC j * (vaughanB U (n / j) : ℂ)) * f n := by
    have hpos : ∀ j ∈ upTo (2 * N), 0 < j := fun j hj =>
      lt_of_lt_of_le one_pos (Finset.mem_Icc.1 hj).1
    have := sum_pairs_eq_sum_dyadic N (upTo (2 * N)) hpos
      (fun j k => U < (j : ℝ) ∧ U < (k : ℝ))
      (fun j k => moebiusC j * (vaughanB U k : ℂ) * f (j * k))
    rw [this]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr ?_ fun j hj => ?_
    · apply Finset.filter_congr
      intro j hj
      have hj0 := Nat.pos_of_mem_divisors hj
      have hjn := Nat.le_of_dvd (mem_dyadic_bounds hn).1 (Nat.dvd_of_mem_divisors hj)
      rw [upTo, Finset.mem_Icc]
      exact ⟨fun h => h.2, fun h => ⟨⟨hj0, le_trans hjn (mem_dyadic_bounds hn).2⟩, h⟩⟩
    · rw [Finset.mem_filter] at hj
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hj.1)]
  simp only [hfilt]
  rw [h1, h2, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : U < (n : ℝ) := by
    simp only [dyadic, intRange, Finset.mem_Ioc, Nat.floor_lt hN] at hn
    exact lt_of_le_of_lt hUN hn.1
  have key := wu_vaughanIdentity_pointwise_holds U n hU hn'
  have key' := congrArg (fun z : ℤ => (z : ℂ)) key
  push_cast at key'
  rw [moebiusC, key']
  simp only [moebiusC]
  ring

end LeanProofs.IntegerPoints
