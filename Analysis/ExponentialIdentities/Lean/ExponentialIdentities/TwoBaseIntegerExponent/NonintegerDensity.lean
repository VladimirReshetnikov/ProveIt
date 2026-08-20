import ExponentialIdentities.TwoBaseIntegerExponent.ZeroDensity

/-!
# Density zero for hypothetical noninteger two-base solutions

This file refines the natural-candidate parametrization by removing the powers of two, which
correspond exactly to the integral exponents.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset Asymptotics Filter

/-- A natural candidate corresponding to a genuinely nonintegral exponent. -/
def TwoBaseNonintegerCandidate (m : ℕ) : Prop :=
  TwoBaseNaturalCandidate m ∧ ¬ ∃ n : ℕ, m = 2 ^ n

/-- For a positive natural value `m`, its associated exponent is integral exactly when `m` is
a power of two. -/
theorem twoBaseCandidateExponent_isInteger_iff_isPowerOfTwo {m : ℕ} (hm : 0 < m) :
    twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ n : ℕ, m = 2 ^ n := by
  constructor
  · rintro ⟨z, hz⟩
    have hxnonneg : 0 ≤ twoBaseCandidateExponent m :=
      IntegerExponent.nonneg_of_two_rpow_integer
        ⟨m, (two_rpow_twoBaseCandidateExponent hm).symm⟩
    have hznonnegR : (0 : ℝ) ≤ z := by rw [hz]; exact hxnonneg
    have hznonneg : 0 ≤ z := by exact_mod_cast hznonnegR
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
    have hz' : (n : ℝ) = twoBaseCandidateExponent m := by
      calc
        (n : ℝ) = (((n : ℕ) : ℤ) : ℝ) := by norm_num
        _ = twoBaseCandidateExponent m := hz
    refine ⟨n, ?_⟩
    have hpow : (m : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
      calc
        (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m :=
          (two_rpow_twoBaseCandidateExponent hm).symm
        _ = (2 : ℝ) ^ (n : ℝ) := by rw [← hz']
        _ = ((2 ^ n : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    exact_mod_cast hpow
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change (n : ℝ) = twoBaseCandidateExponent (2 ^ n)
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    calc
      (2 : ℝ) ^ (n : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_cast
      _ = (2 : ℝ) ^ twoBaseCandidateExponent (2 ^ n) :=
        (two_rpow_twoBaseCandidateExponent (by positivity)).symm

/-- Exact pointwise interpretation of a noninteger natural candidate in the original exponent
problem. -/
theorem twoBaseNonintegerCandidate_iff {m : ℕ} (hm : 0 < m) :
    TwoBaseNonintegerCandidate m ↔
      ((2 : ℝ) ^ twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) ∧
       (3 : ℝ) ^ twoBaseCandidateExponent m ∈ Set.range ((↑) : ℤ → ℝ) ∧
       twoBaseCandidateExponent m ∉ Set.range ((↑) : ℤ → ℝ)) := by
  rw [TwoBaseNonintegerCandidate]
  constructor
  · rintro ⟨hc, hpow⟩
    obtain ⟨h₂, h₃⟩ := hc.integer_powers
    exact ⟨h₂, h₃,
      fun hint ↦ hpow ((twoBaseCandidateExponent_isInteger_iff_isPowerOfTwo hm).mp hint)⟩
  · rintro ⟨_h₂, h₃, hint⟩
    refine ⟨⟨hm, ?_⟩, ?_⟩
    · rw [← three_rpow_twoBaseCandidateExponent hm]
      exact h₃
    · exact fun hpow ↦
        hint ((twoBaseCandidateExponent_isInteger_iff_isPowerOfTwo hm).mpr hpow)

/-- Every noninteger solution of the original two-base problem is represented by a unique
noninteger natural candidate. -/
theorem existsUnique_twoBaseNonintegerCandidate_of_two_three_rpow_integer
    {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃! m : ℕ, TwoBaseNonintegerCandidate m ∧ x = twoBaseCandidateExponent m := by
  obtain ⟨m, hmpos, hm, hxm⟩ :=
    exists_twoBaseNaturalCandidate_of_two_three_rpow_integer h₂ h₃
  have hmnon : ¬ ∃ n : ℕ, m = 2 ^ n := by
    intro hpow
    apply hx
    rw [hxm]
    exact (twoBaseCandidateExponent_isInteger_iff_isPowerOfTwo hmpos).mpr hpow
  refine ⟨m, ⟨⟨hm, hmnon⟩, hxm⟩, ?_⟩
  intro m' hm'
  have hpowequal : (m' : ℝ) = (m : ℝ) := by
    calc
      (m' : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m' :=
        (two_rpow_twoBaseCandidateExponent hm'.1.1.1).symm
      _ = (2 : ℝ) ^ x := by rw [← hm'.2]
      _ = (2 : ℝ) ^ twoBaseCandidateExponent m := by rw [hxm]
      _ = (m : ℝ) := two_rpow_twoBaseCandidateExponent hmpos
  exact_mod_cast hpowequal

/-- Hypothetical noninteger candidate values below `N`. -/
noncomputable def twoBaseNonintegerCandidatesBelow (N : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter TwoBaseNonintegerCandidate

theorem twoBaseNonintegerCandidatesBelow_subset (N : ℕ) :
    twoBaseNonintegerCandidatesBelow N ⊆ twoBaseNaturalCandidatesBelow N := by
  classical
  intro m hm
  simp only [twoBaseNonintegerCandidatesBelow, twoBaseNaturalCandidatesBelow,
    mem_filter, Finset.mem_range] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

/-- Finite Roth-number bound specialized to candidate values corresponding to hypothetical
noninteger solutions. -/
theorem twoBaseNonintegerCandidatesBelow_card_le (N H : ℕ) (hH : 1 ≤ H) :
    (twoBaseNonintegerCandidatesBelow N).card ≤
      H ^ 5 + ((N - H ^ 5) ⌈/⌉ H) * rothNumberNat H := by
  exact (Finset.card_le_card (twoBaseNonintegerCandidatesBelow_subset N)).trans
    (twoBaseNaturalCandidatesBelow_card_le N H hH)

/-- The number of candidate values `m < N` corresponding to noninteger exponents is `o(N)`.
Here density is measured among all natural values of `m = 2 ^ x`, not internally among the
solution set. -/
theorem twoBaseNonintegerCandidatesBelow_isLittleO_id :
    (fun N ↦ ((twoBaseNonintegerCandidatesBelow N).card : ℝ)) =o[atTop]
      (fun N ↦ (N : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [(isLittleO_iff.mp twoBaseNaturalCandidatesBelow_isLittleO_id) hε] with N hN
  simp only [Real.norm_natCast] at hN ⊢
  have hcard : ((twoBaseNonintegerCandidatesBelow N).card : ℝ) ≤
      ((twoBaseNaturalCandidatesBelow N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (twoBaseNonintegerCandidatesBelow_subset N)
  exact hcard.trans hN

/-- Ratio form: hypothetical noninteger candidate values have natural density zero among all
natural values of `m = 2 ^ x`. -/
theorem tendsto_twoBaseNonintegerCandidatesBelow_density_zero :
    Tendsto
      (fun N ↦ ((twoBaseNonintegerCandidatesBelow N).card : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
  twoBaseNonintegerCandidatesBelow_isLittleO_id.tendsto_div_nhds_zero

end LeanProofs.TwoBaseIntegerExponent
