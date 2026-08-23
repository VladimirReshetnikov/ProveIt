import ExponentialIdentities.TwoBaseIntegerExponent.SmoothOutputs

/-!
# The sparse quadratic prime-logarithm class and sparse coaction separation

A two-base solution `m = 2^x`, `n = 3^x` satisfies the quadratic logarithmic relation
`log m · log 3 = log n · log 2`.  Expanding over prime factorizations, the relation is the
evaluation at `(L_p) = (log p)` of the formal quadratic
`𝓕_{m,n} = L(m) L_3 - L(n) L_2`, where `L(u) = ∑_p v_p(u) L_p`.
For an *external* prime `q ∉ {2, 3}` the formal partial derivative is
`∂_q 𝓕 = v_q(m) L_3 - v_q(n) L_2`, whose real evaluation is `log (3^{v_q(m)} / 2^{v_q(n)})`.

This file records the elementary unconditional facts and the conditional implication:

* **External-prime derivative certificate.**  For natural `a, b` not both zero,
  `a log 3 - b log 2 ≠ 0`, with the explicit lower bound `|a log 3 - b log 2| ≥ 1 / max(3^a, 2^b)`.
  So at every external support prime the first coaction descendant of the zero period is a
  nonzero, quantitatively bounded logarithm of a rational number — the hypothetical zero is a
  *transverse* numerical cancellation, not a formal one.
* **Sparse coaction separation implies the conjecture.**  The principle
  `log u · log 3 = log v · log 2 ⟹ v_q(u) log 3 = v_q(v) log 2` for every external prime `q`
  (a very narrow special case of period/coaction stability, stated here as a `Prop`)
  implies the Alaoglu–Erdős conjecture, because the corpus already proves that a nonintegral
  solution has an external prime in the support of `m n`
  (`integer_of_two_three_rpow_integer_of_threeSmooth_outputs`).

* **Calibration.**  Conversely the conjecture implies sparse coaction separation, so the
  principle is *equivalent* to the conjecture (`sparseCoactionSeparation_iff_alaogluErdosConjecture`),
  not a weaker intermediate target.

No claim is made about the truth of sparse coaction separation; the equivalence isolates the
exact missing principle as a named hypothesis and shows it carries no surplus strength.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- `3^a = 2^b` for naturals forces `a = b = 0`. -/
theorem three_pow_eq_two_pow_iff {a b : ℕ} : 3 ^ a = 2 ^ b ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      have h2 : 2 ∣ 3 ^ a := by rw [h]; exact dvd_pow_self 2 hb
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      omega
    subst hb
    have : a = 0 := by
      by_contra ha
      have h3 : 3 ∣ 2 ^ 0 := by rw [← h]; exact dvd_pow_self 3 ha
      simp at h3
    exact ⟨this, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **External-prime derivative certificate.**  For natural `a, b` not both zero,
`a log 3 - b log 2 = log (3^a / 2^b)` is nonzero. -/
theorem external_derivative_ne_zero {a b : ℕ} (hab : ¬ (a = 0 ∧ b = 0)) :
    (a : ℝ) * Real.log 3 - (b : ℝ) * Real.log 2 ≠ 0 := by
  intro h
  have h' : Real.log ((3 : ℝ) ^ a) = Real.log ((2 : ℝ) ^ b) := by
    rw [Real.log_pow, Real.log_pow]; linarith
  have := Real.log_injOn_pos (by simp : (3 : ℝ) ^ a ∈ Set.Ioi 0)
    (by simp : (2 : ℝ) ^ b ∈ Set.Ioi 0) h'
  exact hab (three_pow_eq_two_pow_iff.mp (by exact_mod_cast this))

/-- Elementary quantitative form: `|log (A/B)| ≥ 1 / max A B` for distinct positive naturals. -/
theorem abs_log_div_ge {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B) :
    1 / (max A B : ℝ) ≤ |Real.log A - Real.log B| := by
  wlog hlt : B < A generalizing A B
  · have := this hB hA hne.symm (by omega)
    rwa [max_comm, abs_sub_comm]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  rw [max_eq_left (by exact_mod_cast hlt.le : (B : ℝ) ≤ A)]
  have hpos : 0 ≤ Real.log A - Real.log B := by
    rw [sub_nonneg]; exact Real.log_le_log hBr (by exact_mod_cast hlt.le)
  rw [abs_of_nonneg hpos, ← Real.log_div hAr.ne' hBr.ne']
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hAr hBr)
  have h2 : (1 : ℝ) / A ≤ 1 - ((A : ℝ) / B)⁻¹ := by
    rw [inv_div, div_le_iff₀ hAr, sub_mul, div_mul_cancel₀ _ hAr.ne']
    have : (B : ℝ) + 1 ≤ A := by exact_mod_cast hlt
    linarith
  linarith

/-- `|a log 3 - b log 2| ≥ 1 / max (3^a) (2^b)`: the external derivative is quantitatively
nonzero without any deep Diophantine input. -/
theorem abs_external_derivative_ge {a b : ℕ} (hab : ¬ (a = 0 ∧ b = 0)) :
    1 / (max (3 ^ a) (2 ^ b) : ℝ) ≤ |(a : ℝ) * Real.log 3 - (b : ℝ) * Real.log 2| := by
  have h := abs_log_div_ge (A := 3 ^ a) (B := 2 ^ b) (by positivity) (by positivity)
    (fun h => hab (three_pow_eq_two_pow_iff.mp h))
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow] at h
  push_cast at h ⊢
  exact h

/-- **Sparse coaction separation.**  The hypothesis that a vanishing quadratic prime-logarithm
period is stable under the external prime contractions: whenever
`log u · log 3 = log v · log 2` for positive naturals `u, v`, every prime `q ∉ {2, 3}` satisfies
`v_q(u) log 3 = v_q(v) log 2`.  This is a named, deliberately narrow principle; it is not
asserted. -/
def SparseCoactionSeparation : Prop :=
  ∀ u v : ℕ, 0 < u → 0 < v → Real.log u * Real.log 3 = Real.log v * Real.log 2 →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 →
      (u.factorization q : ℝ) * Real.log 3 = (v.factorization q : ℝ) * Real.log 2

/-- A positive natural that is not of the form `2^a 3^b` has a prime factor outside `{2, 3}`. -/
theorem exists_external_prime_of_not_threeSmooth {u : ℕ} (hu : 0 < u)
    (h : ¬ ∃ a b : ℕ, u = 2 ^ a * 3 ^ b) : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ∣ u := by
  by_contra hcon
  apply h
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hu]
  intro p hp hpd
  by_contra hne
  exact hcon ⟨p, hp, fun h2 => hne (Or.inl h2), fun h3 => hne (Or.inr h3), hpd⟩

/-- **Sparse coaction separation implies the Alaoglu–Erdős conjecture.** -/
theorem alaogluErdosConjecture_of_sparseCoactionSeparation (hSCS : SparseCoactionSeparation) :
    AlaogluErdosConjecture := by
  intro x h₂ h₃
  by_contra hx
  -- Extract the positive natural outputs.
  obtain ⟨zm, hzm⟩ := h₂
  obtain ⟨zn, hzn⟩ := h₃
  have hmpos : 0 < zm := by exact_mod_cast (hzm.symm ▸ Real.rpow_pos_of_pos (by norm_num) x)
  have hnpos : 0 < zn := by exact_mod_cast (hzn.symm ▸ Real.rpow_pos_of_pos (by norm_num) x)
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnpos.le
  have hm : (m : ℝ) = (2 : ℝ) ^ x := by exact_mod_cast hzm
  have hn : (n : ℝ) = (3 : ℝ) ^ x := by exact_mod_cast hzn
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hn0 : 0 < n := by exact_mod_cast hnpos
  -- The quadratic period relation.
  have hrel : Real.log m * Real.log 3 = Real.log n * Real.log 2 := by
    rw [hm, hn, Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)]; ring
  -- A nonintegral solution has an external prime in the support of `m n`.
  have hext : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ (q ∣ m ∨ q ∣ n) := by
    by_cases hms : ∃ a b : ℕ, m = 2 ^ a * 3 ^ b
    · by_cases hns : ∃ c d : ℕ, n = 2 ^ c * 3 ^ d
      · exact absurd (integer_of_two_three_rpow_integer_of_threeSmooth_outputs hm hn hms hns) hx
      · obtain ⟨q, hq, h2, h3, hd⟩ := exists_external_prime_of_not_threeSmooth hn0 hns
        exact ⟨q, hq, h2, h3, Or.inr hd⟩
    · obtain ⟨q, hq, h2, h3, hd⟩ := exists_external_prime_of_not_threeSmooth hm0 hms
      exact ⟨q, hq, h2, h3, Or.inl hd⟩
  obtain ⟨q, hq, hq2, hq3, hqd⟩ := hext
  have hder := hSCS m n hm0 hn0 hrel q hq hq2 hq3
  have hnz : ¬ (m.factorization q = 0 ∧ n.factorization q = 0) := by
    rintro ⟨ha, hb⟩
    rcases hqd with hd | hd
    · exact absurd ha (Nat.Prime.factorization_pos_of_dvd hq hm0.ne' hd).ne'
    · exact absurd hb (Nat.Prime.factorization_pos_of_dvd hq hn0.ne' hd).ne'
  exact external_derivative_ne_zero hnz (by linarith)

/-- **Calibration: the conjecture implies sparse coaction separation.**  If `log u · log 3 =
log v · log 2` for positive naturals `u, v`, then `t = log u / log 2` has `2^t = u` and
`3^t = v`; the conjecture makes `t` an integer, so `u = 2^t`, `v = 3^t` and every external
valuation vanishes. -/
theorem sparseCoactionSeparation_of_alaogluErdosConjecture (hAE : AlaogluErdosConjecture) :
    SparseCoactionSeparation := by
  intro u v hu hv hrel q hq hq2 hq3
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set t : ℝ := Real.log u / Real.log 2 with ht
  have h2t : (2 : ℝ) ^ t = u := by
    rw [Real.rpow_def_of_pos (by norm_num), ht, mul_div_cancel₀ _ hl2.ne', Real.exp_log hur]
  have h3t : (3 : ℝ) ^ t = v := by
    rw [Real.rpow_def_of_pos (by norm_num), ht]
    have : Real.log 3 * (Real.log u / Real.log 2) = Real.log v := by
      field_simp; linarith
    rw [this, Real.exp_log hvr]
  obtain ⟨k, hk⟩ := hAE ⟨u, by rw [h2t]; simp⟩ ⟨v, by rw [h3t]; simp⟩
  -- `t = k ≥ 0` since `u ≥ 1`.
  have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg (by exact_mod_cast hu)) hl2.le
  have hk0 : 0 ≤ k := by exact_mod_cast (hk ▸ ht0 : (0 : ℝ) ≤ k)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have hu' : u = 2 ^ n := by
    have : (u : ℝ) = (2 : ℝ) ^ n := by rw [← h2t, ← hk]; push_cast; rw [Real.rpow_natCast]
    exact_mod_cast this
  have hv' : v = 3 ^ n := by
    have : (v : ℝ) = (3 : ℝ) ^ n := by rw [← h3t, ← hk]; push_cast; rw [Real.rpow_natCast]
    exact_mod_cast this
  have hfu : u.factorization q = 0 := by
    rw [hu', Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_apply]
    simp [Ne.symm hq2]
  have hfv : v.factorization q = 0 := by
    rw [hv', Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_apply]
    simp [Ne.symm hq3]
  rw [hfu, hfv]; simp

/-- **Sparse coaction separation is equivalent to the Alaoglu–Erdős conjecture.**  The
"narrow" period-stability principle is therefore not a weaker intermediate target: it is an
exact reformulation, and its surplus generality (arbitrary `u, v` rather than outputs of one
exponent) is illusory. -/
theorem sparseCoactionSeparation_iff_alaogluErdosConjecture :
    SparseCoactionSeparation ↔ AlaogluErdosConjecture :=
  ⟨alaogluErdosConjecture_of_sparseCoactionSeparation,
    sparseCoactionSeparation_of_alaogluErdosConjecture⟩

end LeanProofs.TwoBaseIntegerExponent
