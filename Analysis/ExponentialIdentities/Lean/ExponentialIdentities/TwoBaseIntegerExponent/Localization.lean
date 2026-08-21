import ExponentialIdentities.TwoBaseIntegerExponent.NonintegerDensity

/-!
# Localization of the two-base conjecture at odd cores

This file formalizes the *localization reformulation*: the Alaoglu--Erd\H{o}s conjecture
is equivalent to the statement that no odd integer `u > 1` admits `a : ℕ` with
`3 ^ a * u ^ (log 3 / log 2) ∈ ℤ` --- equivalently, that `u ^ (log 3 / log 2)` never lies
in `ℤ[1/3]`.

The reduction is exact in both directions: a nonintegral solution `x` yields the odd part
`u` of `2 ^ x` (with `a` its `2`-adic valuation), and conversely any such `(u, a)` yields
the nonintegral solution `x = a + log₂ u`.  The equivalence isolates the transcendence core
of the problem in a single one-number statement: the special case `u = 3` already asks
whether `3 ^ (log 3 / log 2)` can lie in `ℤ[1/3]`, which is open.

Two forms are provided: a purely natural-number form (no candidate with a nontrivial odd
part) and the analytic `ℤ[1/3]`-form.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The base identity `2 ^ (log 3 / log 2) = 3`. -/
theorem two_rpow_logThreeDivLogTwo : (2 : ℝ) ^ logThreeDivLogTwo = 3 := by
  rw [logThreeDivLogTwo, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm,
    div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  exact Real.exp_log (by norm_num)

/-- Splitting the `(log 3 / log 2)`-th power of `2 ^ a * u` into `3 ^ a` times the power of
the odd part. -/
theorem two_pow_mul_rpow_logThreeDivLogTwo (a u : ℕ) (hu : 0 < u) :
    ((2 ^ a * u : ℕ) : ℝ) ^ logThreeDivLogTwo =
      (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  push_cast
  rw [Real.mul_rpow (by positivity) huR.le]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm ((a : ℝ)) logThreeDivLogTwo,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_logThreeDivLogTwo,
    Real.rpow_natCast]

/-- **Localization reformulation, natural-number form.**  The conjecture holds if and only
if no positive multiple of a nontrivial odd number by a power of two is a two-base
candidate. -/
theorem alaogluErdosConjecture_iff_no_odd_multiple_candidate :
    AlaogluErdosConjecture ↔
      ∀ u : ℕ, Odd u → 1 < u → ∀ a : ℕ, ¬ TwoBaseNaturalCandidate (2 ^ a * u) := by
  rw [alaogluErdosConjecture_iff_candidates_are_powers_of_two]
  constructor
  · intro h u hodd hu a hcand
    obtain ⟨k, hk⟩ := h _ hcand
    have hdvd : u ∣ 2 ^ k := ⟨2 ^ a, by rw [← hk]; ring⟩
    have hcop : Nat.Coprime u 2 := by
      rw [Nat.coprime_comm]
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by
        intro h2
        obtain ⟨t, ht⟩ := hodd
        obtain ⟨s, hs⟩ := h2
        omega)
    have hu1 : u = 1 :=
      Nat.dvd_one.mp ((Nat.Coprime.pow_right k hcop) ▸ Nat.dvd_gcd dvd_rfl hdvd)
    omega
  · intro h m hm
    by_cases hpow : ∃ k : ℕ, m = 2 ^ k
    · exact hpow
    · exfalso
      have hm0 : m ≠ 0 := hm.1.ne'
      set a := m.factorization 2 with ha
      set u := ordCompl[2] m with hu
      have hmau : m = 2 ^ a * u := (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
      have hupos : 0 < u := Nat.ordCompl_pos 2 hm0
      have huodd : Odd u := by
        rcases Nat.even_or_odd u with hev | hod
        · exact absurd (hev.two_dvd) (Nat.not_dvd_ordCompl (by norm_num) hm0)
        · exact hod
      have hu1 : 1 < u := by
        rcases Nat.lt_or_ge u 2 with h2 | h2
        · have hone : u = 1 := by omega
          exact absurd ⟨a, by rw [hmau, hone, mul_one]⟩ hpow
        · omega
      exact h u huodd hu1 a (hmau ▸ hm)

/-- **Localization reformulation, `ℤ[1/3]` form.**  The conjecture holds if and only if for
every odd `u > 1` and every `a : ℕ`, the real number `3 ^ a * u ^ (log 3 / log 2)` is not
an integer; equivalently, `u ^ (log 3 / log 2)` never lies in `ℤ[1/3]`. -/
theorem alaogluErdosConjecture_iff_odd_rpow_not_localized :
    AlaogluErdosConjecture ↔
      ∀ u : ℕ, Odd u → 1 < u → ∀ a : ℕ,
        (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo ∉ Set.range ((↑) : ℤ → ℝ) := by
  rw [alaogluErdosConjecture_iff_no_odd_multiple_candidate]
  have hcand : ∀ u : ℕ, 0 < u → ∀ a : ℕ,
      (TwoBaseNaturalCandidate (2 ^ a * u) ↔
        (3 : ℝ) ^ a * (u : ℝ) ^ logThreeDivLogTwo ∈ Set.range ((↑) : ℤ → ℝ)) := by
    intro u hupos a
    constructor
    · intro hc
      have := hc.2
      rwa [two_pow_mul_rpow_logThreeDivLogTwo a u hupos] at this
    · intro hmem
      refine ⟨by positivity, ?_⟩
      rwa [two_pow_mul_rpow_logThreeDivLogTwo a u hupos]
  constructor
  · intro h u hodd hu1 a hmem
    exact h u hodd hu1 a ((hcand u (by omega) a).mpr hmem)
  · intro h u hodd hu1 a hc
    exact h u hodd hu1 a ((hcand u (by omega) a).mp hc)

end LeanProofs.TwoBaseIntegerExponent
