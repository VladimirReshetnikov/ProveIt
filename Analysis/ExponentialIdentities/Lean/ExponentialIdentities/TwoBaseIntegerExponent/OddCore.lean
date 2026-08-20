import ExponentialIdentities.TwoBaseIntegerExponent.CandidateStructure

/-!
# A common odd core for all two-base candidates

The multiplicative rank-two theorem says that the prime exponent vectors of all two-base
candidates span a rational plane containing the vector of `2`.  This file glues the resulting
pairwise power relations into a single global generator: **there is one odd natural number
`w > 1` such that every candidate equals `2 ^ i * w ^ j`.**  The odd part of every candidate
is a power of the same primitive base `w`.

Consequences recorded here:

* every hypothetical nonintegral candidate is `2 ^ i * w ^ j` with `j ≥ 1`;
* in exponent coordinates, every two-base solution has the form `x = i + j * logb 2 w`
  with natural `i`, `j` — a two-generator additive description of the full solution set;
* the global counting bound improves from `(clog 2 N) ^ 2` to `clog 2 N * clog 3 N`;
* each dyadic block `[2 ^ T, 2 ^ (T + 1))` contains at most `clog 3 (2 ^ (T + 1))`
  candidates, i.e. the number of solutions with `x ∈ [T, T + 1)` grows at most linearly
  in `T`, against the quadratic global bound.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset

noncomputable section

/-! ### Odd parts under the candidate power relations -/

private theorem ordCompl_two_pow_eq (x k : ℕ) :
    ordCompl[2] (x ^ k) = (ordCompl[2] x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Nat.ordCompl_mul, ih]

private theorem ordCompl_two_two_pow (u : ℕ) : ordCompl[2] (2 ^ u) = 1 := by
  have h : (2 ^ u).factorization 2 = u := by
    rw [Nat.factorization_pow]
    simp [(by norm_num : Nat.Prime 2).factorization_self]
  rw [h]
  exact Nat.div_self (pow_pos (by norm_num) u)

/-- Relative to a candidate anchor `a` with an odd prime factor `p`, the odd part of any
candidate `m` satisfies an exact power relation with the odd part of `a`. -/
theorem ordCompl_pow_relation {a m p : ℕ}
    (ha : TwoBaseNaturalCandidate a) (hm : TwoBaseNaturalCandidate m)
    (hp : p ≠ 2) (hpa : 0 < a.factorization p) :
    (ordCompl[2] m) ^ a.factorization p = (ordCompl[2] a) ^ m.factorization p := by
  obtain ⟨u, hrel | hrel⟩ := fixed_power_relation_of_odd_prime_factor ha hm hp hpa
  · have h : ordCompl[2] (m ^ a.factorization p) =
        ordCompl[2] (2 ^ u * a ^ m.factorization p) := by rw [hrel]
    rwa [Nat.ordCompl_mul, ordCompl_two_two_pow, one_mul, ordCompl_two_pow_eq,
      ordCompl_two_pow_eq] at h
  · have h : ordCompl[2] (2 ^ u * m ^ a.factorization p) =
        ordCompl[2] (a ^ m.factorization p) := by rw [hrel]
    rwa [Nat.ordCompl_mul, ordCompl_two_two_pow, one_mul, ordCompl_two_pow_eq,
      ordCompl_two_pow_eq] at h

private theorem eq_ordProj_mul_of_ordCompl {m w : ℕ} {j : ℕ}
    (h : ordCompl[2] m = w ^ j) : m = 2 ^ m.factorization 2 * w ^ j := by
  have hself := Nat.ordProj_mul_ordCompl_eq_self m 2
  rw [h] at hself
  exact hself.symm

/-! ### The common odd core -/

/-- **Common odd core.**  There is a single odd natural `w > 1` such that every two-base
candidate value is of the form `2 ^ i * w ^ j`.  (If every candidate is a power of two —
that is, if the Alaoglu--Erdős conjecture holds — any odd base works with `j = 0`;
otherwise `w` is the primitive base of the odd part of any candidate that is not a power
of two.) -/
theorem exists_common_odd_core :
    ∃ w : ℕ, Odd w ∧ 1 < w ∧
      ∀ m : ℕ, TwoBaseNaturalCandidate m → ∃ i j : ℕ, m = 2 ^ i * w ^ j := by
  classical
  by_cases hex : ∃ a, TwoBaseNaturalCandidate a ∧ ordCompl[2] a ≠ 1
  · obtain ⟨a, ha, hoa⟩ := hex
    have ha0 : a ≠ 0 := ha.1.ne'
    have hocpos : 0 < ordCompl[2] a := Nat.ordCompl_pos 2 ha0
    have ho1 : 1 < ordCompl[2] a := by omega
    have hPex : ∃ t : ℕ, 1 < t ∧ ∃ e : ℕ, ordCompl[2] a = t ^ e :=
      ⟨ordCompl[2] a, ho1, 1, (pow_one _).symm⟩
    obtain ⟨w, ⟨hw1, e, hwe⟩, hwmin⟩ :
        ∃ w : ℕ, (1 < w ∧ ∃ e : ℕ, ordCompl[2] a = w ^ e) ∧
          ∀ t : ℕ, t < w → ¬(1 < t ∧ ∃ e : ℕ, ordCompl[2] a = t ^ e) := by
      classical
      exact ⟨Nat.find hPex, Nat.find_spec hPex, fun t ht ↦ Nat.find_min hPex ht⟩
    -- `w` is not a proper perfect power, by minimality.
    have hwnp : ∀ c k : ℕ, 1 < c → 2 ≤ k → w ≠ c ^ k := by
      intro c k hc hk hwck
      have hcw : c < w := by
        have h := Nat.pow_lt_pow_right hc (show 1 < k by omega)
        rw [pow_one] at h
        rw [hwck]
        exact h
      exact hwmin c hcw ⟨hc, k * e, by rw [hwe, hwck, ← pow_mul]⟩
    have he1 : e ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hwe
      omega
    have hwdvd : w ∣ ordCompl[2] a := hwe ▸ dvd_pow_self w he1
    have hwodd : Odd w := by
      rcases Nat.even_or_odd w with hev | hod
      · exact absurd (hev.two_dvd.trans hwdvd)
          (Nat.not_dvd_ordCompl (by norm_num) ha0)
      · exact hod
    -- An odd prime along which the anchor has positive exponent.
    obtain ⟨p, hp, hpdvdo⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ ordCompl[2] a :=
      ⟨(ordCompl[2] a).minFac, Nat.minFac_prime (by omega), (ordCompl[2] a).minFac_dvd⟩
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpdvdo
      exact Nat.not_dvd_ordCompl (by norm_num) ha0 hpdvdo
    have hpa : 0 < a.factorization p := by
      have hpdvda : p ∣ a := hpdvdo.trans (Nat.ordCompl_dvd a 2)
      exact hp.factorization_pos_of_dvd ha0 hpdvda
    refine ⟨w, hwodd, hw1, ?_⟩
    intro m hm
    have hd0 : a.factorization p ≠ 0 := by omega
    have hpoweq : (ordCompl[2] m) ^ a.factorization p =
        w ^ (e * m.factorization p) := by
      rw [ordCompl_pow_relation ha hm hpne2 hpa, hwe, ← pow_mul]
    by_cases hoc1 : ordCompl[2] m = 1
    · exact ⟨m.factorization 2, 0,
        eq_ordProj_mul_of_ordCompl (by rw [hoc1, pow_zero])⟩
    · obtain ⟨c, hoc, hwc⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hd0) hpoweq
      set g := Nat.gcd (a.factorization p) (e * m.factorization p) with hg
      have hgd : g ∣ a.factorization p := Nat.gcd_dvd_left _ _
      have hg0 : g ≠ 0 := fun h0 ↦ hd0 (Nat.eq_zero_of_gcd_eq_zero_left h0)
      have hdg1 : a.factorization p / g = 1 := by
        by_contra hne
        have hdgpos : 0 < a.factorization p / g :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hgd) (by omega)
        have hdg2 : 2 ≤ a.factorization p / g := by omega
        have hc1 : 1 < c := by
          by_contra hle
          have hle' : c ≤ 1 := Nat.not_lt.mp hle
          interval_cases c
          · rw [hwc, zero_pow (by omega : a.factorization p / g ≠ 0)] at hw1
            omega
          · rw [hwc, one_pow] at hw1
            omega
        exact hwnp c (a.factorization p / g) hc1 hdg2 hwc
      have hw_c : w = c := by rw [hwc, hdg1, pow_one]
      exact ⟨m.factorization 2, (e * m.factorization p) / g,
        eq_ordProj_mul_of_ordCompl (by rw [hoc, hw_c])⟩
  · refine ⟨3, ⟨1, by norm_num⟩, by norm_num, ?_⟩
    intro m hm
    have h1 : ordCompl[2] m = 1 := by
      by_contra hne
      exact hex ⟨m, hm, hne⟩
    exact ⟨m.factorization 2, 0,
      eq_ordProj_mul_of_ordCompl (by rw [h1, pow_zero])⟩

/-- Split form of the common odd core: every candidate is either an exact power of two
(an integral solution) or has the form `2 ^ i * w ^ j` with `j ≥ 1`. -/
theorem exists_common_odd_core_split :
    ∃ w : ℕ, Odd w ∧ 1 < w ∧
      ∀ m : ℕ, TwoBaseNaturalCandidate m →
        (∃ n : ℕ, m = 2 ^ n) ∨ ∃ i j : ℕ, 0 < j ∧ m = 2 ^ i * w ^ j := by
  obtain ⟨w, hodd, hw1, hrep⟩ := exists_common_odd_core
  refine ⟨w, hodd, hw1, fun m hm ↦ ?_⟩
  obtain ⟨i, j, hij⟩ := hrep m hm
  cases j with
  | zero => exact Or.inl ⟨i, by simpa using hij⟩
  | succ j' => exact Or.inr ⟨i, j' + 1, j'.succ_pos, hij⟩

/-- **Two-generator description of the solution set.**  In exponent coordinates there is a
single odd `w > 1` such that every real solution of the two integrality conditions has the
form `x = i + j * logb 2 w` with natural numbers `i`, `j`. -/
theorem exists_common_odd_core_exponent :
    ∃ w : ℕ, Odd w ∧ 1 < w ∧
      ∀ x : ℝ,
        (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
        (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) →
        ∃ i j : ℕ, x = i + j * Real.logb 2 w := by
  obtain ⟨w, hodd, hw1, hrep⟩ := exists_common_odd_core
  have hwR : (w : ℝ) ≠ 0 := by
    have hw0 : 0 < w := by omega
    exact_mod_cast hw0.ne'
  refine ⟨w, hodd, hw1, fun x h₂ h₃ ↦ ?_⟩
  obtain ⟨m, hm0, hm, hx⟩ := exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
  obtain ⟨i, j, hij⟩ := hrep m hm
  refine ⟨i, j, ?_⟩
  rw [hx, twoBaseCandidateExponent, hij]
  push_cast
  rw [Real.logb_mul (pow_ne_zero i (by norm_num)) (pow_ne_zero j hwR),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

/-! ### Improved counting bounds -/

/-- Improved global counting: the number of two-base candidates below `N` is at most
`clog 2 N * clog 3 N`, sharpening the earlier `(clog 2 N) ^ 2` bound by the factor
`log 3 / log 2`. -/
theorem twoBaseNaturalCandidatesBelow_card_le_clog_mul_clog (N : ℕ) :
    (twoBaseNaturalCandidatesBelow N).card ≤ Nat.clog 2 N * Nat.clog 3 N := by
  classical
  obtain ⟨w, hwodd, hw1, hwrep⟩ := exists_common_odd_core
  have hw3 : 3 ≤ w := by
    obtain ⟨k, hk⟩ := hwodd
    omega
  have hmem : ∀ m ∈ twoBaseNaturalCandidatesBelow N,
      m < N ∧ TwoBaseNaturalCandidate m := by
    intro m hm
    simpa only [twoBaseNaturalCandidatesBelow, Finset.mem_filter, Finset.mem_range]
      using hm
  set L2 := Nat.clog 2 N with hL2
  set L3 := Nat.clog 3 N with hL3
  have hbounds : ∀ m ∈ twoBaseNaturalCandidatesBelow N, ∀ i j : ℕ,
      m = 2 ^ i * w ^ j → i < L2 ∧ j < L3 := by
    intro m hm i j hij
    obtain ⟨hmN, hcand⟩ := hmem m hm
    constructor
    · apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2
      calc 2 ^ i ≤ 2 ^ i * w ^ j := Nat.le_mul_of_pos_right _ (pow_pos (by omega) j)
        _ = m := hij.symm
        _ < N := hmN
    · apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 3)).2
      calc 3 ^ j ≤ w ^ j := Nat.pow_le_pow_left hw3 j
        _ ≤ 2 ^ i * w ^ j := Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) i)
        _ = m := hij.symm
        _ < N := hmN
  have hrepAll : ∀ m : {m // m ∈ twoBaseNaturalCandidatesBelow N},
      ∃ i j : ℕ, m.1 = 2 ^ i * w ^ j := fun m ↦ hwrep m.1 (hmem m.1 m.2).2
  choose I J hIJ using hrepAll
  let f : {m // m ∈ twoBaseNaturalCandidatesBelow N} → Fin L2 × Fin L3 := fun m ↦
    (⟨I m, (hbounds m.1 m.2 _ _ (hIJ m)).1⟩,
     ⟨J m, (hbounds m.1 m.2 _ _ (hIJ m)).2⟩)
  have hf : Function.Injective f := by
    intro m n hmn
    have hi : I m = I n := by exact congrArg (fun z : Fin L2 × Fin L3 ↦ (z.1 : ℕ)) hmn
    have hj : J m = J n := by exact congrArg (fun z : Fin L2 × Fin L3 ↦ (z.2 : ℕ)) hmn
    apply Subtype.ext
    rw [hIJ m, hIJ n, hi, hj]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hcard

/-- The improved counting bound restricted to hypothetical nonintegral candidates. -/
theorem twoBaseNonintegerCandidatesBelow_card_le_clog_mul_clog (N : ℕ) :
    (twoBaseNonintegerCandidatesBelow N).card ≤ Nat.clog 2 N * Nat.clog 3 N :=
  (Finset.card_le_card (twoBaseNonintegerCandidatesBelow_subset N)).trans
    (twoBaseNaturalCandidatesBelow_card_le_clog_mul_clog N)

/-! ### Linear bound in dyadic blocks -/

/-- Two-base candidates in the dyadic block `[2 ^ T, 2 ^ (T + 1))`; in exponent
coordinates these are exactly the solutions with `x ∈ [T, T + 1)`. -/
noncomputable def twoBaseNaturalCandidatesInDyadicBlock (T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (2 ^ T) (2 ^ (T + 1))).filter TwoBaseNaturalCandidate

private theorem dyadic_pow_unique {T i i' j w : ℕ} (_hw : 0 < w)
    (h1 : 2 ^ T ≤ 2 ^ i * w ^ j) (h2 : 2 ^ i' * w ^ j < 2 ^ (T + 1))
    (hlt : i < i') : False := by
  have hstep : 2 ^ (T + 1) ≤ 2 ^ i' * w ^ j := by
    calc 2 ^ (T + 1) = 2 * 2 ^ T := by ring
      _ ≤ 2 * (2 ^ i * w ^ j) := Nat.mul_le_mul_left 2 h1
      _ = 2 ^ (i + 1) * w ^ j := by ring
      _ ≤ 2 ^ i' * w ^ j :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- **Linear dyadic-block bound.**  Each dyadic block `[2 ^ T, 2 ^ (T + 1))` contains at
most `clog 3 (2 ^ (T + 1))` candidates: the number of two-base solutions with exponent in
`[T, T + 1)` grows at most linearly in `T`, in contrast with the quadratic global bound. -/
theorem twoBaseNaturalCandidatesInDyadicBlock_card_le (T : ℕ) :
    (twoBaseNaturalCandidatesInDyadicBlock T).card ≤ Nat.clog 3 (2 ^ (T + 1)) := by
  classical
  obtain ⟨w, hwodd, hw1, hwrep⟩ := exists_common_odd_core
  have hw3 : 3 ≤ w := by
    obtain ⟨k, hk⟩ := hwodd
    omega
  have hmem : ∀ m ∈ twoBaseNaturalCandidatesInDyadicBlock T,
      (2 ^ T ≤ m ∧ m < 2 ^ (T + 1)) ∧ TwoBaseNaturalCandidate m := by
    intro m hm
    simpa only [twoBaseNaturalCandidatesInDyadicBlock, Finset.mem_filter,
      Finset.mem_Ico] using hm
  set L := Nat.clog 3 (2 ^ (T + 1)) with hL
  have hjbound : ∀ m ∈ twoBaseNaturalCandidatesInDyadicBlock T, ∀ i j : ℕ,
      m = 2 ^ i * w ^ j → j < L := by
    intro m hm i j hij
    obtain ⟨⟨_, hmhi⟩, _⟩ := hmem m hm
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 3)).2
    calc 3 ^ j ≤ w ^ j := Nat.pow_le_pow_left hw3 j
      _ ≤ 2 ^ i * w ^ j := Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) i)
      _ = m := hij.symm
      _ < 2 ^ (T + 1) := hmhi
  have hrepAll : ∀ m : {m // m ∈ twoBaseNaturalCandidatesInDyadicBlock T},
      ∃ i j : ℕ, m.1 = 2 ^ i * w ^ j := fun m ↦ hwrep m.1 (hmem m.1 m.2).2
  choose I J hIJ using hrepAll
  let f : {m // m ∈ twoBaseNaturalCandidatesInDyadicBlock T} → Fin L := fun m ↦
    ⟨J m, hjbound m.1 m.2 _ _ (hIJ m)⟩
  have hf : Function.Injective f := by
    intro m n hmn
    obtain ⟨⟨hmlo, hmhi⟩, _⟩ := hmem m.1 m.2
    obtain ⟨⟨hnlo, hnhi⟩, _⟩ := hmem n.1 n.2
    have hj : J m = J n := by exact congrArg (fun z : Fin L ↦ (z : ℕ)) hmn
    have hi : I m = I n := by
      by_contra hne
      rcases Nat.lt_or_ge (I m) (I n) with hlt | hge
      · exact dyadic_pow_unique (show 0 < w by omega)
          (by rw [← hIJ m]; exact hmlo)
          (by rw [hj, ← hIJ n]; exact hnhi) hlt
      · have hlt' : I n < I m := by omega
        exact dyadic_pow_unique (show 0 < w by omega)
          (by rw [← hIJ n]; exact hnlo)
          (by rw [← hj, ← hIJ m]; exact hmhi) hlt'
    apply Subtype.ext
    rw [hIJ m, hIJ n, hi, hj]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

end

end LeanProofs.TwoBaseIntegerExponent
