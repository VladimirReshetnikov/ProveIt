import GRHArticle.ProgressionFree.IntegerRoughOptimalPrefix
import GRHArticle.ProgressionFree.IntegerRoughTemplateDensity

/-!
# Pasting rules along bands of the largest prime factor

In a progression whose largest prime occurs at most once in each term, that
prime must occur in all three terms. This allows independent admissible
rules on disjoint bands.
-/

namespace GRHArticle.ProgressionFree

open Finset

/-- The largest prime divisor, with value 1 at 0 and 1. -/
def integerLargestPrimeFactor (n : ℕ) : ℕ :=
  max 1 (n.primeFactors.sup id)

theorem one_le_integerLargestPrimeFactor (n : ℕ) :
    1 ≤ integerLargestPrimeFactor n := le_max_left _ _

theorem integerLargestPrimeFactor_le {n : ℕ} (hn : 0 < n) :
    integerLargestPrimeFactor n ≤ n :=
  max_le hn (Finset.sup_le fun _ hp ↦ Nat.le_of_mem_primeFactors hp)

theorem prime_le_integerLargestPrimeFactor {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hd : p ∣ n) : p ≤ integerLargestPrimeFactor n :=
  (Finset.le_sup (f := id) (hp.mem_primeFactors hd hn)).trans (le_max_right _ _)

theorem integerLargestPrimeFactor_prime_dvd {n : ℕ}
    (hn : 1 < integerLargestPrimeFactor n) :
    (integerLargestPrimeFactor n).Prime ∧ integerLargestPrimeFactor n ∣ n := by
  have hne : n.primeFactors.Nonempty := by
    by_contra h
    have h0 : n.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [integerLargestPrimeFactor, h0] at hn
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he' : integerLargestPrimeFactor n = p := by
    simpa [integerLargestPrimeFactor, he] using max_eq_right hp'.one_lt.le
  rw [he']
  exact ⟨hp', Nat.dvd_of_mem_primeFactors hp⟩

theorem integerLargestPrimeFactor_le_iff_smooth {n Y : ℕ} (hn : n ≠ 0) (hY : 1 ≤ Y) :
    integerLargestPrimeFactor n ≤ Y ↔ n ∈ Nat.smoothNumbers (Y+1) := by
  constructor
  · intro h
    refine ⟨hn, ?_⟩
    intro p hp
    obtain ⟨hprime, hd⟩ := (Nat.mem_primeFactorsList hn).mp hp
    exact Nat.lt_succ_of_le ((prime_le_integerLargestPrimeFactor hn hprime hd).trans h)
  · intro h
    refine max_le hY (Finset.sup_le fun p hp ↦ ?_)
    exact Nat.le_of_lt_succ (h.2 p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp))

private theorem factorization_eq_zero_of_largestPrime_lt {n p : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hlt : integerLargestPrimeFactor n < p) : n.factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd
    (fun hd ↦ (not_le_of_gt hlt) (prime_le_integerLargestPrimeFactor hn hp hd))

/-- The integers with largest prime in the interval `(M j, M (j+1)]`. -/
def integerLargestPrimeBand (M : ℕ → ℕ) (j : ℕ) : Set ℕ :=
  {n | M j < integerLargestPrimeFactor n ∧ integerLargestPrimeFactor n ≤ M (j+1)}

/-- Apply rule `j` on the `j`-th largest-prime band. -/
def integerLargestPrimeBandPaste (M : ℕ → ℕ) (E : ℕ → Set ℕ) : Set ℕ :=
  {n | ∃ j, n ∈ E j ∧ n ∈ integerLargestPrimeBand M j}

theorem eq_of_mem_integerLargestPrimeBand {M : ℕ → ℕ} (hM : Monotone M)
    {i j a b : ℕ} (ha : a ∈ integerLargestPrimeBand M i)
    (hb : b ∈ integerLargestPrimeBand M j)
    (he : integerLargestPrimeFactor a = integerLargestPrimeFactor b) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hh := ha.2.trans (hM (Nat.succ_le_of_lt hij))
    exact (not_le_of_gt hb.1 (he ▸ hh)).elim
  · exact hij
  · have hh := hb.2.trans (hM (Nat.succ_le_of_lt hij))
    exact (not_le_of_gt ha.1 (he.symm ▸ hh)).elim

theorem zero_notMem_integerLargestPrimeBandPaste {M : ℕ → ℕ} (hM : Monotone M)
    (hM0 : 1 ≤ M 0) (E : ℕ → Set ℕ) : 0 ∉ integerLargestPrimeBandPaste M E := by
  rintro ⟨j, _, hj⟩
  have h := hj.1
  change M j < max 1 ((0 : ℕ).primeFactors.sup id) at h
  rw [Nat.primeFactors_zero, Finset.sup_empty] at h
  change M j < max 1 0 at h
  rw [max_eq_left (Nat.zero_le 1)] at h
  exact (not_lt_of_ge (hM0.trans (hM (Nat.zero_le j)))) h

/-- Pasting admissible rules preserves either progression convention when the
largest prime occurs with exponent at most one in each relevant rule. -/
theorem integerLargestPrimeBandPaste_admissible {integral : Bool} {M : ℕ → ℕ}
    (hM : Monotone M) (hM0 : 1 ≤ M 0) {E : ℕ → Set ℕ}
    (hE : ∀ j, IntegerPrefixAdmissible integral (E j))
    (hSq : ∀ j n, n ∈ E j → M j < integerLargestPrimeFactor n →
      n.factorization (integerLargestPrimeFactor n) ≤ 1) :
    IntegerPrefixAdmissible integral (integerLargestPrimeBandPaste M E) := by
  intro a b c ha hb hc hab hbc he hd
  have h0 := zero_notMem_integerLargestPrimeBandPaste hM hM0 E
  have hn (n : ℕ) (hn : n ∈ integerLargestPrimeBandPaste M E) : n ≠ 0 :=
    fun hz ↦ h0 (hz ▸ hn)
  obtain ⟨i, hai, ha'⟩ := ha
  obtain ⟨j, hbj, hb'⟩ := hb
  obtain ⟨k, hck, hc'⟩ := hc
  have ha0 := hn a ⟨i, hai, ha'⟩
  have hb0 := hn b ⟨j, hbj, hb'⟩
  have hc0 := hn c ⟨k, hck, hc'⟩
  let p := max (integerLargestPrimeFactor a)
    (max (integerLargestPrimeFactor b) (integerLargestPrimeFactor c))
  have hap : integerLargestPrimeFactor a ≤ p := le_max_left _ _
  have hbp : integerLargestPrimeFactor b ≤ p := (le_max_left _ _).trans (le_max_right _ _)
  have hcp : integerLargestPrimeFactor c ≤ p := (le_max_right _ _).trans (le_max_right _ _)
  have hpa : 1 < integerLargestPrimeFactor a :=
    (hM0.trans (hM (Nat.zero_le i))).trans_lt ha'.1
  have hpb : 1 < integerLargestPrimeFactor b :=
    (hM0.trans (hM (Nat.zero_le j))).trans_lt hb'.1
  have hpc : 1 < integerLargestPrimeFactor c :=
    (hM0.trans (hM (Nat.zero_le k))).trans_lt hc'.1
  have hp_cases : p = integerLargestPrimeFactor a ∨ p = integerLargestPrimeFactor b ∨
      p = integerLargestPrimeFactor c := by
    rcases max_choice (integerLargestPrimeFactor a)
        (max (integerLargestPrimeFactor b) (integerLargestPrimeFactor c)) with h | h
    · exact Or.inl h
    · rcases max_choice (integerLargestPrimeFactor b) (integerLargestPrimeFactor c) with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  have hp : p.Prime := by
    rcases hp_cases with h | h | h
    · rw [h]; exact (integerLargestPrimeFactor_prime_dvd hpa).1
    · rw [h]; exact (integerLargestPrimeFactor_prime_dvd hpb).1
    · rw [h]; exact (integerLargestPrimeFactor_prime_dvd hpc).1
  have exp_le (t n : ℕ) (hn0 : n ≠ 0) (hEt : n ∈ E t)
      (ht : n ∈ integerLargestPrimeBand M t) (hle : integerLargestPrimeFactor n ≤ p) :
      n.factorization p ≤ 1 := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [factorization_eq_zero_of_largestPrime_lt hn0 hp hlt]; exact Nat.zero_le _
    · rw [← heq]; exact hSq t n hEt ht.1
  have hale := exp_le i a ha0 hai ha' hap
  have hble := exp_le j b hb0 hbj hb' hbp
  have hcle := exp_le k c hc0 hck hc' hcp
  have hsome : 0 < a.factorization p ∨ 0 < b.factorization p ∨ 0 < c.factorization p := by
    rcases hp_cases with h | h | h
    · exact Or.inl (hp.factorization_pos_of_dvd ha0 (h.symm ▸ (integerLargestPrimeFactor_prime_dvd hpa).2))
    · exact Or.inr (Or.inl (hp.factorization_pos_of_dvd hb0
        (h.symm ▸ (integerLargestPrimeFactor_prime_dvd hpb).2)))
    · exact Or.inr (Or.inr (hp.factorization_pos_of_dvd hc0
        (h.symm ▸ (integerLargestPrimeFactor_prime_dvd hpc).2)))
  have hfac := congrArg (fun n : ℕ ↦ n.factorization p) he
  simp only [Nat.factorization_mul ha0 hc0, Nat.factorization_mul hb0 hb0,
    Finsupp.add_apply] at hfac
  have haexp : 0 < a.factorization p := by omega
  have hbexp : 0 < b.factorization p := by omega
  have hcexp : 0 < c.factorization p := by omega
  have eq_largest (n : ℕ) (hn0 : n ≠ 0) (hlt : integerLargestPrimeFactor n ≤ p)
      (hexp : 0 < n.factorization p) : integerLargestPrimeFactor n = p := by
    rcases lt_or_eq_of_le hlt with h | h
    · rw [factorization_eq_zero_of_largestPrime_lt hn0 hp h] at hexp
      exact (Nat.lt_irrefl _ hexp).elim
    · exact h
  have hae := eq_largest a ha0 hap haexp
  have hbe := eq_largest b hb0 hbp hbexp
  have hce := eq_largest c hc0 hcp hcexp
  have hij := eq_of_mem_integerLargestPrimeBand hM ha' hb' (hae.trans hbe.symm)
  have hik := eq_of_mem_integerLargestPrimeBand hM ha' hc' (hae.trans hce.symm)
  exact hE i hai (hij.symm ▸ hbj) (hik.symm ▸ hck) hab hbc he hd

/-- The natural-density proof uses fixed smooth templates and squarefree rough
factors. A band beginning above its rule's smooth cutoff meets the required
largest-prime exponent bound. -/
theorem integerLargestPrimeBandPaste_template_admissible {integral : Bool}
    {M Y : ℕ → ℕ} (hM : Monotone M) (hM0 : 1 ≤ M 0)
    (hYM : ∀ j, Y j ≤ M j) {A : ℕ → Set ℕ}
    (hA : ∀ j, IntegerPrefixAdmissible integral (A j))
    (hS : ∀ j, A j ⊆ Nat.smoothNumbers (Y j+1)) :
    IntegerPrefixAdmissible integral (integerLargestPrimeBandPaste M
      (fun j ↦ integerRoughTemplateProducts (integerSquarefreeRoughNumbers (Y j)) (A j))) := by
  apply integerLargestPrimeBandPaste_admissible hM hM0
  · intro j
    exact integerRoughTemplate_admissible integral (Y j)
      (integerSquarefreeRoughNumbers (Y j)) (fun _ ↦ A j)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) (fun _ _ ↦ hS j) (fun _ _ ↦ hA j)
  · rintro j n ⟨r, s, hr, hs, rfl⟩ hD
    let p := integerLargestPrimeFactor (r*s)
    have hp : p.Prime := (integerLargestPrimeFactor_prime_dvd
      ((hM0.trans (hM (Nat.zero_le j))).trans_lt hD)).1
    have hs' := hS j hs
    have hzero : s.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun hd ↦ by
      have hsmall := Nat.mem_smoothNumbers'.mp hs' p hp hd
      have hlarge : Y j < p := (hYM j).trans_lt hD
      omega
    change (r*s).factorization p ≤ 1
    rw [Nat.factorization_mul hr.1.1 (Nat.ne_zero_of_mem_smoothNumbers hs'),
      Finsupp.add_apply, hzero, add_zero]
    exact hr.2.natFactorization_le_one p

end GRHArticle.ProgressionFree
