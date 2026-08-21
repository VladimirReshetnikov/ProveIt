import ExponentialIdentities.TwoBaseIntegerExponent.ArithmeticRigidity
import ExponentialIdentities.TwoBaseIntegerExponent.NonintegerDensity

/-!
# A least hypothetical noninteger solution and its primitivity

Although the Alaoglu--Erdős conjecture remains open, failure would produce a *least*
noninteger solution.  The reason is arithmetic rather than topological: solutions are
parametrized by the natural value `m = 2 ^ x`, so the well-ordering of `ℕ` applies.

Leastness turns the existing affine-descent lemmas into exact primitivity statements for
the least output pair.  It has no common matched base depth, no common perfect-power degree,
and, more generally, no nontrivial simultaneous affine decomposition.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The two integrality conditions, packaged as a predicate on the exponent. -/
def TwoBaseIntegralSolution (x : ℝ) : Prop :=
  (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ) ∧
    (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ)

/-- A genuinely nonintegral solution of the two-base problem. -/
def TwoBaseNonintegerSolution (x : ℝ) : Prop :=
  TwoBaseIntegralSolution x ∧ x ∉ Set.range ((↑) : ℤ → ℝ)

/-- A least noninteger solution: it is no larger than every other noninteger solution. -/
def IsLeastTwoBaseNonintegerSolution (x : ℝ) : Prop :=
  TwoBaseNonintegerSolution x ∧ ∀ y : ℝ, TwoBaseNonintegerSolution y → x ≤ y

/-- Any nonempty collection of noninteger natural candidates has a least member. -/
theorem exists_least_twoBaseNonintegerCandidate
    (hex : ∃ m : ℕ, TwoBaseNonintegerCandidate m) :
    ∃ m : ℕ, TwoBaseNonintegerCandidate m ∧
      ∀ n : ℕ, TwoBaseNonintegerCandidate n → m ≤ n := by
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro n hn
  exact Nat.find_min' hex hn

/-- If the Alaoglu--Erdős conjecture fails, there is a positive least noninteger real
solution.  This can be combined with any finite zero-free theorem (currently the bound `12`)
without making the order-theoretic construction depend on a large finite certificate. -/
theorem exists_least_twoBaseNonintegerSolution
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, IsLeastTwoBaseNonintegerSolution β ∧ 0 < β := by
  classical
  have hexsol : ∃ x : ℝ, TwoBaseNonintegerSolution x := by
    unfold AlaogluErdosConjecture at hfail
    push Not at hfail
    obtain ⟨x, h₂, h₃, hx⟩ := hfail
    exact ⟨x, ⟨⟨h₂, h₃⟩, hx⟩⟩
  obtain ⟨x, hx⟩ := hexsol
  obtain ⟨m, hm, hxm⟩ :=
    existsUnique_twoBaseNonintegerCandidate_of_two_three_rpow_integer
      hx.1.1 hx.1.2 hx.2
  have hexcand : ∃ m : ℕ, TwoBaseNonintegerCandidate m := ⟨m, hm.1⟩
  obtain ⟨m₀, hm₀, hm₀min⟩ := exists_least_twoBaseNonintegerCandidate hexcand
  let β := twoBaseCandidateExponent m₀
  have hm₀pos : 0 < m₀ := hm₀.1.1
  have hβsol : TwoBaseNonintegerSolution β := by
    have hm₀' := (twoBaseNonintegerCandidate_iff hm₀pos).mp hm₀
    exact ⟨⟨hm₀'.1, hm₀'.2.1⟩, hm₀'.2.2⟩
  have hβmin : ∀ y : ℝ, TwoBaseNonintegerSolution y → β ≤ y := by
    intro y hy
    obtain ⟨n, hn, _hnuniq⟩ :=
      existsUnique_twoBaseNonintegerCandidate_of_two_three_rpow_integer
        hy.1.1 hy.1.2 hy.2
    have hmn : m₀ ≤ n := hm₀min n hn.1
    by_contra hnot
    have hyβ : y < β := lt_of_not_ge hnot
    have hp := (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 2)) hyβ
    rw [hn.2] at hp
    change (2 : ℝ) ^ twoBaseCandidateExponent n <
      (2 : ℝ) ^ twoBaseCandidateExponent m₀ at hp
    rw [two_rpow_twoBaseCandidateExponent hn.1.1.1,
      two_rpow_twoBaseCandidateExponent hm₀pos] at hp
    exact (not_lt_of_ge (by exact_mod_cast hmn)) hp
  refine ⟨β, ⟨hβsol, hβmin⟩, ?_⟩
  have hnonneg : 0 ≤ β :=
    IntegerExponent.nonneg_of_two_rpow_integer hβsol.1.1
  have hne : β ≠ 0 := by
    intro hzero
    apply hβsol.2
    refine ⟨0, ?_⟩
    simp [hzero]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The least noninteger solution is unique. -/
theorem IsLeastTwoBaseNonintegerSolution.unique
    {x y : ℝ} (hx : IsLeastTwoBaseNonintegerSolution x)
    (hy : IsLeastTwoBaseNonintegerSolution y) : x = y :=
  le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-- Every noninteger solution, and hence in particular the least one, is positive. -/
theorem IsLeastTwoBaseNonintegerSolution.pos
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β) : 0 < β := by
  have hnonneg : 0 ≤ β :=
    IntegerExponent.nonneg_of_two_rpow_integer hβ.1.1.1
  have hne : β ≠ 0 := by
    intro hzero
    apply hβ.1.2
    refine ⟨0, ?_⟩
    simp [hzero]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The integral output pair of a least noninteger solution cannot simultaneously contain
one factor of its respective bases. -/
theorem IsLeastTwoBaseNonintegerSolution.not_both_base_dvd_outputs
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {m n : ℕ}
    (hm : (m : ℝ) = (2 : ℝ) ^ β)
    (hn : (n : ℝ) = (3 : ℝ) ^ β) :
    ¬(2 ∣ m ∧ 3 ∣ n) := by
  rintro ⟨h2m, h3n⟩
  obtain ⟨h₂, h₃⟩ := shifted_integral_powers_of_common_divisibility (r := 1)
    hm hn (by simpa using h2m) (by simpa using h3n)
  have hnon : β - 1 ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hβ.1.2
    refine ⟨z + 1, ?_⟩
    push_cast
    linarith
  have hle := hβ.2 (β - 1)
    ⟨⟨by simpa using h₂, by simpa using h₃⟩, hnon⟩
  linarith

/-- The outputs of a least noninteger solution cannot both be perfect `k`-th powers for
any `k ≥ 2`. -/
theorem IsLeastTwoBaseNonintegerSolution.no_common_perfect_power
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b k : ℕ} (hk : 2 ≤ k)
    (hm : ((a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hn : ((b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    False := by
  have hβpos := hβ.pos
  obtain ⟨h₂, h₃⟩ :=
    divided_exponent_integral_powers_of_common_perfect_power (by omega) hm hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnon : β / (k : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hβ.1.2
    refine ⟨(k : ℤ) * z, ?_⟩
    push_cast
    rw [hz]
    field_simp
  have hle := hβ.2 (β / (k : ℝ)) ⟨⟨h₂, h₃⟩, hnon⟩
  have hkone : (1 : ℝ) < k := by exact_mod_cast hk
  have hlt : β / (k : ℝ) < β := by
    exact (div_lt_iff₀ hkR).2 (by nlinarith)
  exact (not_lt_of_ge hle) hlt

/-- Exact affine primitivity of the least output pair.  A simultaneous representation
`2 ^ r * a ^ k`, `3 ^ r * b ^ k` forces the trivial parameters `r = 0`, `k = 1`. -/
theorem IsLeastTwoBaseNonintegerSolution.affine_primitive
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b r k : ℕ} (hk : 0 < k)
    (hm : ((2 ^ r * a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hn : ((3 ^ r * b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    r = 0 ∧ k = 1 := by
  have hβpos := hβ.pos
  obtain ⟨h₂, h₃⟩ := affine_descent_integral_powers hk hm hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnon :
      (β - (r : ℝ)) / (k : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    apply hβ.1.2
    refine ⟨(r : ℤ) + (k : ℤ) * z, ?_⟩
    push_cast
    rw [hz]
    field_simp
    ring
  have hle := hβ.2 ((β - (r : ℝ)) / (k : ℝ))
    ⟨⟨h₂, h₃⟩, hnon⟩
  have hr0 : r = 0 := by
    by_contra hr
    have hrR : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero hr)
    have hlt : (β - (r : ℝ)) / (k : ℝ) < β := by
      apply (div_lt_iff₀ hkR).2
      have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_le_mul_of_nonneg_left hkone hβpos.le]
    exact (not_lt_of_ge hle) hlt
  subst r
  have hk1 : k = 1 := by
    by_contra hkne
    have hk2 : 2 ≤ k := by omega
    have hlt : β / (k : ℝ) < β := by
      apply (div_lt_iff₀ hkR).2
      have hkone : (1 : ℝ) < k := by exact_mod_cast hk2
      nlinarith
    have hle' : β ≤ β / (k : ℝ) := by simpa using hle
    exact (not_lt_of_ge hle') hlt
  exact ⟨rfl, hk1⟩

/-- If the Alaoglu--Erdős conjecture fails, there is a unique positive least noninteger
solution, and every simultaneous affine decomposition of its two outputs is trivial. -/
theorem existsUnique_pos_leastTwoBaseNonintegerSolution_and_affine_primitive
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃! β : ℝ,
      IsLeastTwoBaseNonintegerSolution β ∧ 0 < β ∧
        ∀ {a b r k : ℕ}, 0 < k →
          ((2 ^ r * a ^ k : ℕ) : ℝ) = (2 : ℝ) ^ β →
          ((3 ^ r * b ^ k : ℕ) : ℝ) = (3 : ℝ) ^ β →
          r = 0 ∧ k = 1 := by
  obtain ⟨β, hβ, hβpos⟩ := exists_least_twoBaseNonintegerSolution hfail
  refine ⟨β, ⟨hβ, hβpos, ?_⟩, ?_⟩
  · intro a b r k hk hm hn
    exact hβ.affine_primitive hk hm hn
  · intro γ hγ
    exact hγ.1.unique hβ

end LeanProofs.TwoBaseIntegerExponent
