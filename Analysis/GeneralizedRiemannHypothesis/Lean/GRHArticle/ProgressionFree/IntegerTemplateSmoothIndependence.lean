import GRHArticle.ProgressionFree.IntegerSmoothIndependence

/-!
# Uniform estimates for finite squarefree-rough templates

A finite smooth template is an exact finite valuation test. Excluding
the squares of the rough primes up to one extra cutoff gives a finite
divisibility rule. The remaining prime squares have uniformly small mass.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset
open scoped Classical

private theorem roughPart_factorization_small {Y n p : ℕ} (hp : p.Prime) (hpY : p ≤ Y) :
    (integerRoughPart Y n).factorization p = 0 := by
  have h := integerRoughPart_mem Y n
  refine Nat.factorization_eq_zero_of_not_dvd fun hd ↦ ?_
  exact (not_lt_of_ge hpY)
    (h.2 p ((Nat.mem_primeFactorsList_iff_dvd h.1 hp).mpr hd))

private theorem smoothPart_factorization_large {Y n p : ℕ} (hp : p.Prime) (hpY : Y < p) :
    (integerSmoothPart Y n).factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hd ↦ by
    have hh := Nat.mem_smoothNumbers'.mp (integerSmoothPart_mem Y n) p hp hd
    omega

private theorem factorization_eq_parts {Y n p : ℕ} (hn : n ≠ 0) :
    n.factorization p =
      (integerSmoothPart Y n).factorization p + (integerRoughPart Y n).factorization p := by
  have h := congrArg (fun k : ℕ ↦ k.factorization p)
    (integerSmoothPart_mul_roughPart Y hn).symm
  simpa only [Nat.factorization_mul (integerSmoothPart_mem Y n).1
    (integerRoughPart_mem Y n).1, Finsupp.add_apply] using h

private theorem smoothPart_eq_iff_valuationCylinder {Y n s : ℕ} (hn : n ≠ 0)
    (hs : s ∈ Nat.smoothNumbers (Y+1)) :
    integerSmoothPart Y n = s ↔
      n ∈ valuationCylinder (Nat.primesLE Y) (fun p ↦ s.factorization p) := by
  have hsmall (p : ℕ) (hp : p ∈ Nat.primesLE Y) :
      n.factorization p = (integerSmoothPart Y n).factorization p := by
    obtain ⟨hpY, hp⟩ := Nat.mem_primesLE.mp hp
    rw [factorization_eq_parts hn, roughPart_factorization_small hp hpY, add_zero]
  constructor
  · intro he
    exact ⟨hn, fun p hp ↦ he ▸ hsmall p hp⟩
  · intro h
    apply Nat.factorization_inj (integerSmoothPart_mem Y n).1 hs.1
    ext p
    by_cases hp' : p.Prime
    · by_cases hpY : p ≤ Y
      · have hp := Nat.mem_primesLE.mpr ⟨hpY, hp'⟩
        exact (hsmall p hp).symm.trans (h.2 p hp)
      · rw [smoothPart_factorization_large hp' (lt_of_not_ge hpY),
          Nat.factorization_eq_zero_of_not_dvd
            (fun hpS ↦ hpY (Nat.le_of_lt_succ (Nat.mem_smoothNumbers'.mp hs p hp' hpS)))]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp',
        Nat.factorization_eq_zero_of_not_prime _ hp']

private theorem squarefree_roughPart_iff {Y n : ℕ} (hn : n ≠ 0) :
    Squarefree (integerRoughPart Y n) ↔ ∀ p : ℕ, Y < p → p.Prime → ¬ p^2 ∣ n := by
  have hp_dvd (p : ℕ) (hpY : Y < p) (hp : p.Prime) :
      p^2 ∣ integerRoughPart Y n ↔ p^2 ∣ n := by
    rw [hp.pow_dvd_iff_le_factorization (integerRoughPart_mem Y n).1,
      hp.pow_dvd_iff_le_factorization hn, factorization_eq_parts hn,
      smoothPart_factorization_large hp hpY, zero_add]
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h p hpY hp hpd
    exact h p hp (by simpa only [pow_two] using (hp_dvd p hpY hp).mpr hpd)
  · intro h p hp hpd
    by_cases hpY : Y < p
    · exact h p hpY hp ((hp_dvd p hpY hp).mp (by simpa only [pow_two] using hpd))
    · have hd : p ∣ p*p := dvd_mul_right _ _
      exact hpY ((integerRoughPart_mem Y n).2 p
        ((Nat.mem_primeFactorsList_iff_dvd (integerRoughPart_mem Y n).1 hp).mpr
          (hd.trans hpd)))

private theorem mem_squarefreeRoughTemplate_iff {Y n : ℕ} {A : Set ℕ}
    (hn : n ≠ 0) (hA : A ⊆ Nat.smoothNumbers (Y+1)) :
    n ∈ integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A ↔
      integerSmoothPart Y n ∈ A ∧ Squarefree (integerRoughPart Y n) := by
  constructor
  · rintro ⟨r,s,hr,hs,rfl⟩
    rw [integerSmoothPart_mul_of_parts hr.1 (hA hs), integerRoughPart_mul_of_parts hr.1 (hA hs)]
    exact ⟨hs, hr.2⟩
  · rintro ⟨hS, hR⟩
    refine ⟨integerRoughPart Y n, integerSmoothPart Y n, ⟨integerRoughPart_mem Y n, hR⟩, hS, ?_⟩
    rw [mul_comm, integerSmoothPart_mul_roughPart Y hn]

private def largePrimeSquares (K : ℕ) : Set ℕ :=
  {n | ∃ p : ℕ, K < p ∧ p.Prime ∧ p^2 ∣ n}

private def primeSquareCutoffs (Y K : ℕ) : Finset ℕ :=
  (Nat.primesLE K).filter (Y < ·)

private def truncatedRoughTemplate (Y K : ℕ) (A : Finset ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ integerSmoothPart Y n ∈ A ∧
    ∀ p ∈ primeSquareCutoffs Y K, ¬ p^2 ∣ n}

private theorem truncatedRoughTemplate_expansion (Y K : ℕ) {A : Finset ℕ}
    (hA : (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1)) :
    IntegerDivisibilityExpansion (truncatedRoughTemplate Y K A) := by
  have hhead := IntegerDivisibilityExpansion.exists_finset A
    (fun s ↦ valuationCylinder (Nat.primesLE Y) (fun p ↦ s.factorization p))
    (fun s _ ↦ IntegerDivisibilityExpansion.valuationCylinder _ _
      (fun p hp ↦ (Nat.mem_primesLE.mp hp).2))
  have htail := IntegerDivisibilityExpansion.forall_finset (primeSquareCutoffs Y K)
    (fun p ↦ {n | p^2 ∣ n}ᶜ)
    (fun p hp ↦ (IntegerDivisibilityExpansion.dvd
      (pow_pos (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.pos _)).compl)
  apply (hhead.inter htail).congr
  intro n hn
  constructor
  · rintro ⟨⟨s,hs,hc⟩,ht⟩
    have hh := (smoothPart_eq_iff_valuationCylinder hn.ne' (hA hs)).mpr hc
    exact ⟨hn.ne', hh.symm ▸ hs, fun p hp ↦ ht p hp⟩
  · rintro ⟨_, hs, ht⟩
    exact ⟨⟨integerSmoothPart Y n, hs,
      (smoothPart_eq_iff_valuationCylinder hn.ne' (hA hs)).mp rfl⟩, fun p hp ↦ ht p hp⟩

private theorem squarefreeRoughTemplate_subset_truncated {Y K : ℕ} {A : Finset ℕ}
    (hA : (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1)) :
    integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A ⊆
      truncatedRoughTemplate Y K A := by
  intro n hn
  obtain ⟨r,s,hr,hs,he⟩ := hn
  have hn0 : n ≠ 0 := he ▸ mul_ne_zero hr.1.1 (hA hs).1
  obtain ⟨hS,hR⟩ := (mem_squarefreeRoughTemplate_iff hn0 hA).mp ⟨r,s,hr,hs,he⟩
  refine ⟨hn0,hS, fun p hp ↦ ?_⟩
  obtain ⟨hpK,hpY⟩ := mem_filter.mp hp
  exact (squarefree_roughPart_iff hn0).mp hR p hpY (Nat.mem_primesLE.mp hpK).2

private theorem densityUpTo_abs_template_sub_truncated {Y K : ℕ} (hK : 0 < K) {A : Finset ℕ}
    (hA : (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1)) (B : Set ℕ) (N : ℕ) :
    |densityUpTo (integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A ∩ B) N -
      densityUpTo (truncatedRoughTemplate Y K A ∩ B) N| ≤ 1/(K : ℝ) := by
  refine (densityUpTo_abs_sub_le_of_symmDiff_subset (E := largePrimeSquares K) N ?_).trans
    (densityUpTo_largePrimeSquare_le K N hK)
  intro n hn
  rcases hn with h | h
  · exfalso
    exact h.2 ⟨squarefreeRoughTemplate_subset_truncated hA h.1.1,h.1.2⟩
  · obtain ⟨hn0,hS,hT⟩ := h.1.1
    have hF : ¬ Squarefree (integerRoughPart Y n) := fun hs ↦
      h.2 ⟨(mem_squarefreeRoughTemplate_iff hn0 hA).2 ⟨hS,hs⟩,h.1.2⟩
    rw [squarefree_roughPart_iff hn0] at hF
    push Not at hF
    obtain ⟨p,hpY,hp,hpd⟩ := hF
    by_cases hpK : K < p
    · exact ⟨p,hpK,hp,hpd⟩
    · exact (hT p (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨le_of_not_gt hpK,hp⟩, hpY⟩) hpd).elim

/-- Finite squarefree-rough templates have a uniform smoothness estimate with
their true natural densities. -/
theorem hasUniformSmoothDensity_integerRoughTemplateProducts {Y : ℕ} {A : Finset ℕ}
    (hA : (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1)) {e : ℝ}
    (he : HasNaturalDensity (integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A) e) :
    HasUniformSmoothDensity (integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A) e := by
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_one_div_lt (show 0 < ε/4 by positivity)
  let k := K+1
  have hk : 0 < k := Nat.succ_pos _
  have hk' : 1/(k : ℝ) < ε/4 := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using hK
  let E := integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) (A : Set ℕ)
  let C := truncatedRoughTemplate Y k A
  obtain ⟨c,hc⟩ := (truncatedRoughTemplate_expansion Y k hA).exists_hasUniformSmoothDensity
  have hc' : HasNaturalDensity C c := hc.hasNaturalDensity
  have hdiff (B : Set ℕ) (N : ℕ) :
      |densityUpTo (E ∩ B) N - densityUpTo (C ∩ B) N| ≤ 1/(k : ℝ) :=
    densityUpTo_abs_template_sub_truncated hk hA B N
  have hec : |e-c| ≤ 1/(k : ℝ) := by
    apply le_of_tendsto ((he.sub hc').abs)
    exact Eventually.of_forall fun N ↦ by simpa only [Set.inter_univ] using hdiff Set.univ N
  obtain ⟨M,hM⟩ := hc (ε/4) (by positivity)
  refine ⟨M, fun N Z hN hZ ↦ ?_⟩
  let S := Nat.smoothNumbers (Z+1)
  let w := densityUpTo S N
  have hw0 : 0 ≤ w := densityUpTo_nonneg _ _
  have hw1 : w ≤ 1 := densityUpTo_le_one _ _
  have hcd := hM N Z hN hZ
  have hEd := hdiff S N
  have hce : |c*w-e*w| ≤ 1/(k : ℝ) := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hw0, abs_sub_comm]
    exact (mul_le_of_le_one_right (abs_nonneg _) hw1).trans hec
  change |densityUpTo (E ∩ S) N - e*w| < ε
  have htri := abs_sub_le (densityUpTo (E ∩ S) N) (densityUpTo (C ∩ S) N) (e*w)
  have htri' := abs_sub_le (densityUpTo (C ∩ S) N) (c*w) (e*w)
  linarith

/-- A version of the uniform bound directly in terms of the largest prime
factor, for selecting the band thresholds of the pasting construction. -/
theorem eventually_integerRoughTemplateProducts_largestPrime_independent {Y : ℕ} {A : Finset ℕ}
    (hA : (A : Set ℕ) ⊆ Nat.smoothNumbers (Y+1)) {e : ℝ}
    (he : HasNaturalDensity (integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A) e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N Z : ℕ, M ≤ N → M ≤ Z →
      |densityUpTo (integerRoughTemplateProducts (integerSquarefreeRoughNumbers Y) A ∩
        {n | integerLargestPrimeFactor n ≤ Z}) N -
        e * densityUpTo {n | integerLargestPrimeFactor n ≤ Z} N| ≤ ε := by
  obtain ⟨M,hM⟩ := hasUniformSmoothDensity_integerRoughTemplateProducts hA he ε hε
  refine ⟨max M 1, fun N Z hN hZ ↦ ?_⟩
  have hZ1 := (le_max_right M 1).trans hZ
  have hcongr (B : Set ℕ) :
      densityUpTo (B ∩ {n | integerLargestPrimeFactor n ≤ Z}) N =
        densityUpTo (B ∩ Nat.smoothNumbers (Z+1)) N := by
    apply le_antisymm <;> apply densityUpTo_le_of_subset_on_cutoff
    · intro n hn h
      exact ⟨h.1, (integerLargestPrimeFactor_le_iff_smooth
        (Nat.ne_of_gt (mem_Icc.mp hn).1) hZ1).mp h.2⟩
    · intro n hn h
      exact ⟨h.1, (integerLargestPrimeFactor_le_iff_smooth
        (Nat.ne_of_gt (mem_Icc.mp hn).1) hZ1).mpr h.2⟩
  have hi : densityUpTo {n | integerLargestPrimeFactor n ≤ Z} N =
      densityUpTo (Nat.smoothNumbers (Z+1)) N := by
    simpa only [Set.univ_inter] using hcongr Set.univ
  rw [hcongr,hi]
  exact (hM N Z ((le_max_left M 1).trans hN) ((le_max_left M 1).trans hZ)).le

end GRHArticle.ProgressionFree
