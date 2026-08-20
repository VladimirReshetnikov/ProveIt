import ExponentialIdentities.TwoBaseIntegerExponent.MultiplicativeRank

open scoped BigOperators Nat

/-!
# Structure and conditional abundance of two-base candidates

The rank-two theorem becomes especially concrete because `2` is itself a candidate.  After
fixing any candidate `a` with an odd prime factor `p`, the odd-prime exponent profile of every
candidate is proportional to that of `a`.  Unique factorization then says that a fixed power of
each candidate differs from a power of `a` only by a power of two.

Conversely, multiplicative closure produces the injective boxes `2 ^ i * a ^ j`.  Thus the
logarithmic-square upper bound is conditionally of the correct order if a non-power-of-two
candidate exists.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

private theorem twoBaseNaturalCandidate_two : TwoBaseNaturalCandidate 2 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨by norm_num, ⟨3, ?_⟩⟩
  change (3 : ℝ) = (2 : ℝ) ^ logThreeDivLogTwo
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- Relative to an odd prime occurring in one candidate, all candidates have proportional
odd-prime factorization profiles. -/
theorem odd_factorization_cross_mul
    {a b p q : ℕ}
    (ha : TwoBaseNaturalCandidate a)
    (hb : TwoBaseNaturalCandidate b)
    (hp : p ≠ 2) (hpa : 0 < a.factorization p) (hq : q ≠ 2) :
    a.factorization p * b.factorization q =
      b.factorization p * a.factorization q := by
  have hdep := not_linearIndependent_primeExponentVector_of_three_candidates
    twoBaseNaturalCandidate_two ha hb
  obtain ⟨g, hg, hgnz⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hcoord (r : ℕ) :
      g 0 * primeExponentVector 2 r +
          g 1 * primeExponentVector a r +
          g 2 * primeExponentVector b r = 0 := by
    have hg' := hg
    rw [Fin.sum_univ_three] at hg'
    have hr := congrArg (fun v : ℕ →₀ ℚ ↦ v r) hg'
    simpa [threePrimeExponentVectors] using hr
  have hv2p : primeExponentVector 2 p = 0 := by
    simp only [primeExponentVector, Finsupp.mapRange_apply]
    rw [(by norm_num : Nat.Prime 2).factorization]
    simp [hp]
  have hv2q : primeExponentVector 2 q = 0 := by
    simp only [primeExponentVector, Finsupp.mapRange_apply]
    rw [(by norm_num : Nat.Prime 2).factorization]
    simp [hq]
  have hv22 : primeExponentVector 2 2 = 1 := by
    simp [primeExponentVector, (by norm_num : Nat.Prime 2).factorization_self]
  have hvaP : primeExponentVector a p ≠ 0 := by
    simp only [primeExponentVector, Finsupp.mapRange_apply]
    exact_mod_cast hpa.ne'
  have hg2 : g 2 ≠ 0 := by
    intro hg2
    have hpEq := hcoord p
    rw [hv2p, mul_zero, zero_add, hg2, zero_mul, add_zero] at hpEq
    have hg1 : g 1 = 0 := (mul_eq_zero.mp hpEq).resolve_right hvaP
    have h2Eq := hcoord 2
    simp [hv22, hg1, hg2] at h2Eq
    have hg0 : g 0 = 0 := h2Eq
    obtain ⟨i, hi⟩ := hgnz
    fin_cases i <;> contradiction
  have hpEq := hcoord p
  have hqEq := hcoord q
  rw [hv2p, mul_zero, zero_add] at hpEq
  rw [hv2q, mul_zero, zero_add] at hqEq
  have hcrossQ :
      (a.factorization p : ℚ) * (b.factorization q : ℚ) =
        (b.factorization p : ℚ) * (a.factorization q : ℚ) := by
    simp only [primeExponentVector, Finsupp.mapRange_apply] at hpEq hqEq
    have hmul : g 2 *
        ((a.factorization p : ℚ) * (b.factorization q : ℚ) -
          (b.factorization p : ℚ) * (a.factorization q : ℚ)) = 0 := by
      linear_combination (a.factorization p : ℚ) * hqEq -
        (a.factorization q : ℚ) * hpEq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hg2)
  exact_mod_cast hcrossQ

/-- If `d` is the exponent of an odd prime in a candidate `a`, then the `d`-th power of
every candidate differs from the corresponding power of `a` only by a power of two. -/
theorem fixed_power_relation_of_odd_prime_factor
    {a b p : ℕ}
    (ha : TwoBaseNaturalCandidate a)
    (hb : TwoBaseNaturalCandidate b)
    (hp : p ≠ 2) (hpa : 0 < a.factorization p) :
    ∃ u : ℕ,
      b ^ a.factorization p = 2 ^ u * a ^ b.factorization p ∨
      2 ^ u * b ^ a.factorization p = a ^ b.factorization p := by
  let d := a.factorization p
  let n := b.factorization p
  let eb := d * b.factorization 2
  let ea := n * a.factorization 2
  have ha0 : a ≠ 0 := ha.1.ne'
  have hb0 : b ≠ 0 := hb.1.ne'
  have hodd (q : ℕ) (hq : q ≠ 2) :
      d * b.factorization q = n * a.factorization q := by
    exact odd_factorization_cross_mul ha hb hp hpa hq
  by_cases hle : ea ≤ eb
  · refine ⟨eb - ea, Or.inl ?_⟩
    apply Nat.eq_of_factorization_eq (pow_ne_zero _ hb0)
      (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (pow_ne_zero _ ha0))
    intro q
    rw [Nat.factorization_pow, Nat.factorization_mul
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (pow_ne_zero _ ha0),
      Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, nsmul_eq_mul, Finsupp.add_apply]
    rw [(by norm_num : Nat.Prime 2).factorization]
    by_cases hq : q = 2
    · subst q
      simp only [Finsupp.single_eq_same, mul_one]
      exact_mod_cast (Nat.sub_add_cancel hle).symm
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hq), mul_zero, zero_add]
      exact_mod_cast hodd q hq
  · have hle' : eb ≤ ea := by omega
    refine ⟨ea - eb, Or.inr ?_⟩
    apply Nat.eq_of_factorization_eq
      (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (pow_ne_zero _ hb0))
      (pow_ne_zero _ ha0)
    intro q
    rw [Nat.factorization_mul
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) (pow_ne_zero _ hb0),
      Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    rw [(by norm_num : Nat.Prime 2).factorization]
    by_cases hq : q = 2
    · subst q
      simp only [Finsupp.single_eq_same, mul_one]
      exact_mod_cast Nat.sub_add_cancel hle'
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hq), mul_zero, zero_add]
      exact_mod_cast hodd q hq

private theorem twoBaseNaturalCandidate_one : TwoBaseNaturalCandidate 1 := by
  refine ⟨by norm_num, ⟨1, ?_⟩⟩
  norm_num

private theorem TwoBaseNaturalCandidate.mul {a b : ℕ}
    (ha : TwoBaseNaturalCandidate a) (hb : TwoBaseNaturalCandidate b) :
    TwoBaseNaturalCandidate (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  obtain ⟨za, hza⟩ := ha.2
  obtain ⟨zb, hzb⟩ := hb.2
  refine ⟨za * zb, ?_⟩
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), ← hza, ← hzb]

private theorem TwoBaseNaturalCandidate.pow {a : ℕ}
    (ha : TwoBaseNaturalCandidate a) (n : ℕ) :
    TwoBaseNaturalCandidate (a ^ n) := by
  induction n with
  | zero => simpa using twoBaseNaturalCandidate_one
  | succ n ih => simpa [pow_succ] using ih.mul ha

/-- A non-power-of-two candidate generates an injective two-dimensional box of candidates.
This conditionally matches the logarithmic-square upper bound in order of magnitude. -/
theorem twoBaseNaturalCandidatesBelow_card_ge_box
    {a p : ℕ}
    (ha : TwoBaseNaturalCandidate a)
    (hp : p ≠ 2) (hpa : 0 < a.factorization p)
    (k l : ℕ) :
    k * l ≤ (twoBaseNaturalCandidatesBelow (2 ^ k * a ^ l)).card := by
  classical
  have ha1 : 1 < a := by
    have ha_pos : 0 < a := ha.1
    have ha_ne_one : a ≠ 1 := by
      intro haone
      subst a
      rw [Nat.factorization_one] at hpa
      simp at hpa
    omega
  let f : Fin k × Fin l →
      {m // m ∈ twoBaseNaturalCandidatesBelow (2 ^ k * a ^ l)} := fun ij ↦
    ⟨2 ^ (ij.1 : ℕ) * a ^ (ij.2 : ℕ), by
      simp only [twoBaseNaturalCandidatesBelow, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) ij.1.isLt)
          (pow_pos ha.1 _)).trans
          (Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right ha1 ij.2.isLt)
            (pow_pos (by norm_num : 0 < (2 : ℕ)) _))
      · exact (twoBaseNaturalCandidate_two.pow _).mul (ha.pow _)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hval : 2 ^ (i : ℕ) * a ^ (j : ℕ) =
        2 ^ (i' : ℕ) * a ^ (j' : ℕ) := congrArg Subtype.val hij
    have hfac := congrArg (fun m : ℕ ↦ m.factorization p) hval
    simp only [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
        (pow_ne_zero _ ha.1.ne'), Nat.factorization_pow, Finsupp.add_apply,
        Finsupp.smul_apply, nsmul_eq_mul] at hfac
    rw [(by norm_num : Nat.Prime 2).factorization] at hfac
    simp [hp] at hfac
    have hj : (j : ℕ) = (j' : ℕ) := by
      rcases hfac with hfac | hzero
      · exact hfac
      · exact False.elim (hpa.ne' hzero)
    have hiPow : 2 ^ (i : ℕ) = 2 ^ (i' : ℕ) := by
      rw [hj] at hval
      exact Nat.eq_of_mul_eq_mul_right (pow_pos ha.1 _) hval
    have hi : (i : ℕ) = (i' : ℕ) := Nat.pow_right_injective (by norm_num) hiPow
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using hcard

/-- Using a positive power of the anchor in each box entry gives the same conditional
quadratic lower bound for genuinely noninteger candidates. -/
theorem twoBaseNonintegerCandidatesBelow_card_ge_box
    {a p : ℕ}
    (ha : TwoBaseNaturalCandidate a)
    (hp : p ≠ 2) (hpa : 0 < a.factorization p)
    (k l : ℕ) :
    k * l ≤
      (twoBaseNonintegerCandidatesBelow (2 ^ k * a ^ (l + 1))).card := by
  classical
  have ha1 : 1 < a := by
    have ha_pos : 0 < a := ha.1
    have ha_ne_one : a ≠ 1 := by
      intro haone
      subst a
      rw [Nat.factorization_one] at hpa
      simp at hpa
    omega
  let f : Fin k × Fin l →
      {m // m ∈ twoBaseNonintegerCandidatesBelow (2 ^ k * a ^ (l + 1))} := fun ij ↦
    ⟨2 ^ (ij.1 : ℕ) * a ^ ((ij.2 : ℕ) + 1), by
      simp only [twoBaseNonintegerCandidatesBelow, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) ij.1.isLt)
          (pow_pos ha.1 _)).trans
          (Nat.mul_lt_mul_of_pos_left
            (Nat.pow_lt_pow_right ha1 (Nat.add_lt_add_right ij.2.isLt 1))
            (pow_pos (by norm_num : 0 < (2 : ℕ)) _))
      · refine ⟨(twoBaseNaturalCandidate_two.pow _).mul (ha.pow _), ?_⟩
        rintro ⟨n, hn⟩
        have hfac := congrArg (fun m : ℕ ↦ m.factorization p) hn
        simp only [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
            (pow_ne_zero _ ha.1.ne'), Nat.factorization_pow, Finsupp.add_apply,
            Finsupp.smul_apply, nsmul_eq_mul] at hfac
        rw [(by norm_num : Nat.Prime 2).factorization] at hfac
        simp [hp] at hfac
        exact hpa.ne' hfac⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hval : 2 ^ (i : ℕ) * a ^ ((j : ℕ) + 1) =
        2 ^ (i' : ℕ) * a ^ ((j' : ℕ) + 1) := congrArg Subtype.val hij
    have hfac := congrArg (fun m : ℕ ↦ m.factorization p) hval
    simp only [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
        (pow_ne_zero _ ha.1.ne'), Nat.factorization_pow, Finsupp.add_apply,
        Finsupp.smul_apply, nsmul_eq_mul] at hfac
    rw [(by norm_num : Nat.Prime 2).factorization] at hfac
    simp [hp] at hfac
    have hj : (j : ℕ) = (j' : ℕ) := by
      rcases hfac with hfac | hzero
      · omega
      · exact False.elim (hpa.ne' hzero)
    have hiPow : 2 ^ (i : ℕ) = 2 ^ (i' : ℕ) := by
      rw [hj] at hval
      exact Nat.eq_of_mul_eq_mul_right (pow_pos ha.1 _) hval
    have hi : (i : ℕ) = (i' : ℕ) := Nat.pow_right_injective (by norm_num) hiPow
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using hcard

end

end LeanProofs.TwoBaseIntegerExponent
