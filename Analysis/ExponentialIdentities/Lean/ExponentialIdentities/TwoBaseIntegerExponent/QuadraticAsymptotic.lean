import ExponentialIdentities.TwoBaseIntegerExponent.ExactCounting

/-!
# Sharp quadratic candidate-count asymptotics

Conditional on the exact primitive-generator description, the exact floor sum for the
first `T` dyadic candidate blocks is squeezed within `T` of its quadratic main term.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Filter Set
open scoped BigOperators Topology

noncomputable section

/-- Splitting the candidate finset below `2 ^ (T + 1)` at the dyadic boundary `2 ^ T`. -/
theorem twoBaseNaturalCandidatesBelow_two_pow_succ (T : ℕ) :
    twoBaseNaturalCandidatesBelow (2 ^ (T + 1)) =
      twoBaseNaturalCandidatesBelow (2 ^ T) ∪
        twoBaseNaturalCandidatesInDyadicBlock T := by
  classical
  ext m
  simp only [twoBaseNaturalCandidatesBelow, twoBaseNaturalCandidatesInDyadicBlock,
    Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro ⟨hm, hcand⟩
    by_cases hlo : m < 2 ^ T
    · exact Or.inl ⟨hlo, hcand⟩
    · exact Or.inr ⟨⟨by omega, hm⟩, hcand⟩
  · rintro (⟨hm, hcand⟩ | ⟨⟨_, hm⟩, hcand⟩)
    · exact ⟨hm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)), hcand⟩
    · exact ⟨hm, hcand⟩

/-- The lower candidate finset and the next dyadic block are disjoint. -/
theorem twoBaseNaturalCandidatesBelow_disjoint_dyadicBlock (T : ℕ) :
    Disjoint (twoBaseNaturalCandidatesBelow (2 ^ T))
      (twoBaseNaturalCandidatesInDyadicBlock T) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmBelow hmBlock
  simp only [twoBaseNaturalCandidatesBelow, Finset.mem_filter, Finset.mem_range] at hmBelow
  simp only [twoBaseNaturalCandidatesInDyadicBlock, Finset.mem_filter,
    Finset.mem_Ico] at hmBlock
  omega

/-- The cumulative dyadic-block count is exactly the number of candidates below `2 ^ T`. -/
theorem cumulativeTwoBaseCandidateCount_eq_card_below_two_pow (T : ℕ) :
    cumulativeTwoBaseCandidateCount T =
      (twoBaseNaturalCandidatesBelow (2 ^ T)).card := by
  classical
  induction T with
  | zero =>
      have hempty : twoBaseNaturalCandidatesBelow 1 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hlt := Finset.mem_range.mp hm'.1
        have hpos := hm'.2.1
        omega
      simp [cumulativeTwoBaseCandidateCount, hempty]
  | succ T ih =>
      rw [cumulativeTwoBaseCandidateCount, Finset.sum_range_succ]
      rw [twoBaseNaturalCandidatesBelow_two_pow_succ]
      rw [Finset.card_union_of_disjoint
        (twoBaseNaturalCandidatesBelow_disjoint_dyadicBlock T)]
      rw [← ih, cumulativeTwoBaseCandidateCount]

/-- The real sum of the first `T` positive natural numbers. -/
private theorem sum_range_natCast_add_one (T : ℕ) :
    ∑ N ∈ Finset.range T, ((N : ℝ) + 1) =
      (T : ℝ) * ((T : ℝ) + 1) / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The sharp quadratic main term for the cumulative candidate count. -/
def quadraticCandidateMainTerm (β : ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) * ((T : ℝ) + 1) / (2 * β)

/-- The exact cumulative floor sum differs from its quadratic main term by at most `T`. -/
theorem cumulativeTwoBaseCandidateCount_quadratic_bounds
    {β : ℝ} (hβpos : 0 < β) (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℕ) :
    quadraticCandidateMainTerm β T ≤ (cumulativeTwoBaseCandidateCount T : ℝ) ∧
      (cumulativeTwoBaseCandidateCount T : ℝ) ≤
        quadraticCandidateMainTerm β T + T := by
  have hsum :
      ∑ N ∈ Finset.range T, (((N : ℝ) + 1) / β) =
        quadraticCandidateMainTerm β T := by
    rw [← Finset.sum_div, sum_range_natCast_add_one]
    simp only [quadraticCandidateMainTerm]
    field_simp
  have hfloorUpper : ∀ N : ℕ,
      (⌊((N : ℝ) + 1) / β⌋₊ : ℝ) ≤ ((N : ℝ) + 1) / β := by
    intro N
    exact Nat.floor_le (by positivity)
  have hfloorLower : ∀ N : ℕ,
      ((N : ℝ) + 1) / β ≤ (⌊((N : ℝ) + 1) / β⌋₊ : ℝ) + 1 := by
    intro N
    exact (Nat.lt_floor_add_one _).le
  have hsumUpper :
      (∑ N ∈ Finset.range T, (⌊((N : ℝ) + 1) / β⌋₊ : ℝ)) ≤
        ∑ N ∈ Finset.range T, ((N : ℝ) + 1) / β := by
    exact Finset.sum_le_sum fun N _ ↦ hfloorUpper N
  have hsumLower :
      (∑ N ∈ Finset.range T, ((N : ℝ) + 1) / β) ≤
        ∑ N ∈ Finset.range T,
          ((⌊((N : ℝ) + 1) / β⌋₊ : ℝ) + 1) := by
    exact Finset.sum_le_sum fun N _ ↦ hfloorLower N
  have hcountReal :
      (cumulativeTwoBaseCandidateCount T : ℝ) =
        (T : ℝ) +
          ∑ N ∈ Finset.range T, (⌊((N : ℝ) + 1) / β⌋₊ : ℝ) := by
    exact_mod_cast cumulativeTwoBaseCandidateCount_eq hβpos hβirr hchar T
  constructor
  · rw [← hsum]
    calc
      (∑ N ∈ Finset.range T, ((N : ℝ) + 1) / β) ≤
          ∑ N ∈ Finset.range T,
            ((⌊((N : ℝ) + 1) / β⌋₊ : ℝ) + 1) := hsumLower
      _ = (T : ℝ) +
          ∑ N ∈ Finset.range T, (⌊((N : ℝ) + 1) / β⌋₊ : ℝ) := by
            simp [Finset.sum_add_distrib, add_comm]
      _ = (cumulativeTwoBaseCandidateCount T : ℝ) := hcountReal.symm
  · calc
      (cumulativeTwoBaseCandidateCount T : ℝ) =
          (T : ℝ) +
            ∑ N ∈ Finset.range T, (⌊((N : ℝ) + 1) / β⌋₊ : ℝ) := hcountReal
      _ ≤ (T : ℝ) +
          ∑ N ∈ Finset.range T, ((N : ℝ) + 1) / β := by gcongr
      _ = quadraticCandidateMainTerm β T + T := by rw [hsum]; ring

/-- Sharp conditional quadratic asymptotic for the cumulative dyadic candidate count. -/
theorem tendsto_cumulativeTwoBaseCandidateCount_div_sq
    {β : ℝ} (hβpos : 0 < β) (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β) :
    Tendsto
      (fun T : ℕ ↦ (cumulativeTwoBaseCandidateCount T : ℝ) / (T : ℝ) ^ 2)
      atTop (nhds (1 / (2 * β))) := by
  have hinv : Tendsto (fun T : ℕ ↦ ((T : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto
      (fun T : ℕ ↦ quadraticCandidateMainTerm β T / (T : ℝ) ^ 2)
      atTop (nhds (1 / (2 * β))) := by
    have hformula :
        (fun T : ℕ ↦ quadraticCandidateMainTerm β T / (T : ℝ) ^ 2) =ᶠ[atTop]
          (fun T : ℕ ↦ (1 / (2 * β)) * (1 + ((T : ℝ))⁻¹)) := by
      filter_upwards [eventually_atTop.2 ⟨1, fun T hT ↦ hT⟩] with T hT
      have hT0 : (T : ℝ) ≠ 0 := by positivity
      simp only [quadraticCandidateMainTerm]
      field_simp
    apply Tendsto.congr' hformula.symm
    simpa using
      (tendsto_const_nhds.mul (tendsto_const_nhds.add hinv) :
        Tendsto (fun T : ℕ ↦ (1 / (2 * β)) * (1 + ((T : ℝ))⁻¹))
          atTop (nhds ((1 / (2 * β)) * (1 + 0))))
  have hupper : Tendsto
      (fun T : ℕ ↦ quadraticCandidateMainTerm β T / (T : ℝ) ^ 2 +
        ((T : ℝ))⁻¹)
      atTop (nhds (1 / (2 * β))) := by
    simpa using hmain.add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hupper ?_ ?_
  · filter_upwards [eventually_atTop.2 ⟨1, fun T hT ↦ hT⟩] with T hT
    have hden : 0 < (T : ℝ) ^ 2 := by positivity
    exact (div_le_div_iff_of_pos_right hden).2
      (cumulativeTwoBaseCandidateCount_quadratic_bounds hβpos hβirr hchar T).1
  · filter_upwards [eventually_atTop.2 ⟨1, fun T hT ↦ hT⟩] with T hT
    have hden : 0 < (T : ℝ) ^ 2 := by positivity
    have hb :=
      (cumulativeTwoBaseCandidateCount_quadratic_bounds hβpos hβirr hchar T).2
    calc
      (cumulativeTwoBaseCandidateCount T : ℝ) / (T : ℝ) ^ 2 ≤
          (quadraticCandidateMainTerm β T + T) / (T : ℝ) ^ 2 :=
        (div_le_div_iff_of_pos_right hden).2 hb
      _ = quadraticCandidateMainTerm β T / (T : ℝ) ^ 2 + ((T : ℝ))⁻¹ := by
        have hT0 : (T : ℝ) ≠ 0 := by positivity
        field_simp

/-- Sharp conditional quadratic asymptotic for actual candidates below `2 ^ T`. -/
theorem tendsto_twoBaseNaturalCandidatesBelow_two_pow_div_sq
    {β : ℝ} (hβpos : 0 < β) (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β) :
    Tendsto
      (fun T : ℕ ↦
        ((twoBaseNaturalCandidatesBelow (2 ^ T)).card : ℝ) / (T : ℝ) ^ 2)
      atTop (nhds (1 / (2 * β))) := by
  simpa only [cumulativeTwoBaseCandidateCount_eq_card_below_two_pow] using
    tendsto_cumulativeTwoBaseCandidateCount_div_sq hβpos hβirr hchar

/-- Failure of the conjecture supplies its canonical least generator and the corresponding
positive sharp quadratic counting constant. -/
theorem exists_leastGenerator_with_candidate_quadratic_asymptotic
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      (∀ x : ℝ, TwoBaseIntegralSolution x ↔
        ∃! nk : ℕ × ℕ, x = (nk.1 : ℝ) + (nk.2 : ℝ) * β) ∧
      Tendsto
        (fun T : ℕ ↦
          ((twoBaseNaturalCandidatesBelow (2 ^ T)).card : ℝ) / (T : ℝ) ^ 2)
        atTop (nhds (1 / (2 * β))) := by
  obtain ⟨β, hβirr, hβleast, hunique, _⟩ :=
    exists_primitiveGenerator_with_exact_counting hfail
  have hinj : Function.Injective
      (fun nk : ℕ × ℕ ↦ (nk.1 : ℝ) + (nk.2 : ℝ) * β) :=
    IntegerExponent.Irrational.injective_nat_add_mul hβirr
  have hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β := by
    intro x
    constructor
    · intro hx
      obtain ⟨nk, hnk, _⟩ := (hunique x).mp hx
      exact ⟨nk.1, nk.2, hnk⟩
    · rintro ⟨n, k, hnk⟩
      apply (hunique x).mpr
      refine ⟨(n, k), hnk, ?_⟩
      intro nk hnk'
      apply hinj
      exact hnk'.symm.trans hnk
  exact ⟨β, hβirr, hβleast, hunique,
    tendsto_twoBaseNaturalCandidatesBelow_two_pow_div_sq hβleast.pos hβirr hchar⟩

/-- Every integral power of two is a two-base natural candidate. -/
private theorem twoBaseNaturalCandidate_two_pow (T : ℕ) :
    TwoBaseNaturalCandidate (2 ^ T) := by
  have h₂ : (2 : ℝ) ^ (T : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := by
    refine ⟨((2 ^ T : ℕ) : ℤ), ?_⟩
    norm_num [Real.rpow_natCast]
  have h₃ : (3 : ℝ) ^ (T : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := by
    refine ⟨((3 ^ T : ℕ) : ℤ), ?_⟩
    norm_num [Real.rpow_natCast]
  obtain ⟨m, hmpos, hm, hTm⟩ :=
    exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
  have hmcast : (m : ℝ) = ((2 ^ T : ℕ) : ℝ) := by
    rw [← two_rpow_twoBaseCandidateExponent hmpos, ← hTm, Real.rpow_natCast]
    norm_num
  have hmEq : m = 2 ^ T := by exact_mod_cast hmcast
  rwa [hmEq] at hm

/-- Under the conjecture, every dyadic block contains exactly its left-endpoint power of two. -/
theorem twoBaseNaturalCandidatesInDyadicBlock_eq_singleton_of_alaogluErdosConjecture
    (hconj : AlaogluErdosConjecture) (T : ℕ) :
    twoBaseNaturalCandidatesInDyadicBlock T = {2 ^ T} := by
  classical
  ext m
  simp only [twoBaseNaturalCandidatesInDyadicBlock, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hmlo, hmhi⟩, hm⟩
    obtain ⟨n, hn⟩ :=
      (alaogluErdosConjecture_iff_candidates_are_powers_of_two.mp hconj) m hm
    subst m
    have hTn : T ≤ n :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hmlo
    have hnT : n < T + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hmhi
    congr
    omega
  · rintro rfl
    exact ⟨⟨le_rfl,
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)⟩,
      twoBaseNaturalCandidate_two_pow T⟩

/-- If the conjecture holds, the first `T` dyadic blocks contain exactly `T` candidates. -/
theorem cumulativeTwoBaseCandidateCount_eq_of_alaogluErdosConjecture
    (hconj : AlaogluErdosConjecture) (T : ℕ) :
    cumulativeTwoBaseCandidateCount T = T := by
  simp only [cumulativeTwoBaseCandidateCount,
    twoBaseNaturalCandidatesInDyadicBlock_eq_singleton_of_alaogluErdosConjecture hconj,
    Finset.card_singleton]
  simp

/-- If the conjecture holds, there are exactly `T` candidates below `2 ^ T`. -/
theorem twoBaseNaturalCandidatesBelow_two_pow_card_of_alaogluErdosConjecture
    (hconj : AlaogluErdosConjecture) (T : ℕ) :
    (twoBaseNaturalCandidatesBelow (2 ^ T)).card = T := by
  rw [← cumulativeTwoBaseCandidateCount_eq_card_below_two_pow]
  exact cumulativeTwoBaseCandidateCount_eq_of_alaogluErdosConjecture hconj T

/-- Under the conjecture, the candidate count below `2 ^ T` is subquadratic (indeed, exactly
linear). -/
theorem tendsto_twoBaseNaturalCandidatesBelow_two_pow_div_sq_zero_of_alaogluErdosConjecture
    (hconj : AlaogluErdosConjecture) :
    Tendsto
      (fun T : ℕ ↦
        ((twoBaseNaturalCandidatesBelow (2 ^ T)).card : ℝ) / (T : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun T : ℕ ↦ ((T : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hformula :
      (fun T : ℕ ↦
        ((twoBaseNaturalCandidatesBelow (2 ^ T)).card : ℝ) / (T : ℝ) ^ 2) =ᶠ[atTop]
        (fun T : ℕ ↦ ((T : ℝ))⁻¹) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun T hT ↦ hT⟩] with T hT
    rw [twoBaseNaturalCandidatesBelow_two_pow_card_of_alaogluErdosConjecture hconj]
    have hT0 : (T : ℝ) ≠ 0 := by positivity
    field_simp
  exact Tendsto.congr' hformula.symm hinv

/-- **Growth reformulation of Alaoglu--Erdős.** The conjecture is equivalent to
subquadratic growth, along dyadic cutoffs, of the natural candidate count. If it fails, the
preceding sharp asymptotic gives a strictly positive quadratic density in the logarithmic
parameter. -/
theorem alaogluErdosConjecture_iff_candidate_count_below_two_pow_subquadratic :
    AlaogluErdosConjecture ↔
      Tendsto
        (fun T : ℕ ↦
          ((twoBaseNaturalCandidatesBelow (2 ^ T)).card : ℝ) / (T : ℝ) ^ 2)
        atTop (nhds 0) := by
  constructor
  · exact
      tendsto_twoBaseNaturalCandidatesBelow_two_pow_div_sq_zero_of_alaogluErdosConjecture
  · intro hzero
    by_contra hfail
    obtain ⟨β, _, hβleast, _, hpositive⟩ :=
      exists_leastGenerator_with_candidate_quadratic_asymptotic hfail
    have heq : 1 / (2 * β) = 0 := tendsto_nhds_unique hpositive hzero
    have hβpos : 0 < β := hβleast.pos
    have hconstpos : 0 < 1 / (2 * β) := by positivity
    linarith

end

end LeanProofs.TwoBaseIntegerExponent
