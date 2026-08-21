import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import Mathlib.Algebra.Order.Round

/-!
# Compact synchronized orbit reformulation of the Alaoglu--Erdős conjecture

Under failure of the conjecture the primitive generator `β` produces the two integers
`M = 2 ^ β` and `A = 3 ^ β`, and every natural multiple `k * β` is again a solution.  Dividing
`M ^ k = 2 ^ (k β)` and `A ^ k = 3 ^ (k β)` by the *same* denominator `2 ^ ⌊k β⌋`, resp.
`3 ^ ⌊k β⌋`, therefore leaves the pair

`(M ^ k / 2 ^ ⌊k β⌋, A ^ k / 3 ^ ⌊k β⌋) = (2 ^ {k β}, 3 ^ {k β})`,

which lies on the compact arc `𝒜 = {(2 ^ t, 3 ^ t) : 0 ≤ t < 1}` for every `k`.  The point of
this reformulation is that the *floor exponent is shared by both coordinates*: a single integer
`⌊k β⌋` synchronizes the two denominators.  This is the feature a bespoke `S`-integral counting
theorem would have to exploit.

The converse is elementary and is what makes the reformulation exact.  Arc membership at the
index `k` supplies `t_k ∈ [0, 1)` with

`M ^ k = 2 ^ (t_k + ⌊k β⌋)`  and  `A ^ k = 3 ^ (t_k + ⌊k β⌋)`.

Taking `k = 1` gives a single real `γ` with `M = 2 ^ γ` and `A = 3 ^ γ`; injectivity of
`t ↦ 2 ^ t` upgrades this to `k γ = t_k + ⌊k β⌋` for all `k ≥ 1`.  Both `k γ - ⌊k β⌋` and
`k β - ⌊k β⌋` then lie in `[0, 1)`, so `k * |γ - β| < 1` for every `k ≥ 1`; the Archimedean
property of `ℝ` forces `γ = β`.  Hence `2 ^ β = M` and `3 ^ β = A` are integers while `β` is
irrational, that is, the conjecture fails.

The main results are `not_alaogluErdosConjecture_iff_exists_compactOrbit` and its positive
restatement `alaogluErdosConjecture_iff_no_compactOrbit`.  The forward direction is recorded
separately, in the sharper form
`exists_canonical_compactOrbit_of_not_alaogluErdosConjecture`, which additionally exhibits `β`
as the *least* noninteger solution and gives the orbit condition for every `k`, not only for
`k ≥ 1`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The compact arc `𝒜 = {(2 ^ t, 3 ^ t) : 0 ≤ t < 1}` traced by the two-base exponential map
over the unit interval.  It is the closure-free half-open parametrization used in the report. -/
def compactExponentialArc : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ p = ((2 : ℝ) ^ t, (3 : ℝ) ^ t)}

/-- Coordinatewise description of membership in the compact arc. -/
theorem mem_compactExponentialArc {u v : ℝ} :
    (u, v) ∈ compactExponentialArc ↔
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ u = (2 : ℝ) ^ t ∧ v = (3 : ℝ) ^ t := by
  constructor
  · rintro ⟨t, ht0, ht1, ht⟩
    exact ⟨t, ht0, ht1, congrArg (fun p : ℝ × ℝ ↦ p.1) ht,
      congrArg (fun p : ℝ × ℝ ↦ p.2) ht⟩
  · rintro ⟨t, ht0, ht1, hu, hv⟩
    exact ⟨t, ht0, ht1, by rw [hu, hv]⟩

/-- The synchronized `S`-integral orbit point `(M ^ k / 2 ^ ⌊k β⌋, A ^ k / 3 ^ ⌊k β⌋)`.  Both
coordinates are divided by a power of their own base whose exponent is the *same* integer
`⌊k β⌋`. -/
def synchronizedOrbitPoint (M A : ℕ) (β : ℝ) (k : ℕ) : ℝ × ℝ :=
  ((M : ℝ) ^ k / (2 : ℝ) ^ ⌊(k : ℝ) * β⌋,
    (A : ℝ) ^ k / (3 : ℝ) ^ ⌊(k : ℝ) * β⌋)

/-- Unfolded form of arc membership for a synchronized orbit point. -/
theorem mem_compactExponentialArc_synchronizedOrbitPoint (M A : ℕ) (β : ℝ) (k : ℕ) :
    synchronizedOrbitPoint M A β k ∈ compactExponentialArc ↔
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
        (M : ℝ) ^ k / (2 : ℝ) ^ ⌊(k : ℝ) * β⌋ = (2 : ℝ) ^ t ∧
        (A : ℝ) ^ k / (3 : ℝ) ^ ⌊(k : ℝ) * β⌋ = (3 : ℝ) ^ t := by
  constructor
  · rintro ⟨t, ht0, ht1, ht⟩
    exact ⟨t, ht0, ht1, congrArg (fun p : ℝ × ℝ ↦ p.1) ht,
      congrArg (fun p : ℝ × ℝ ↦ p.2) ht⟩
  · rintro ⟨t, ht0, ht1, hu, hv⟩
    refine ⟨t, ht0, ht1, ?_⟩
    show ((M : ℝ) ^ k / (2 : ℝ) ^ ⌊(k : ℝ) * β⌋,
        (A : ℝ) ^ k / (3 : ℝ) ^ ⌊(k : ℝ) * β⌋) = ((2 : ℝ) ^ t, (3 : ℝ) ^ t)
    rw [hu, hv]

/-- Dividing `b ^ (k β)` by `b ^ ⌊k β⌋` leaves exactly `b ^ {k β}`. -/
private theorem rpow_pow_div_zpow_floor {b : ℝ} (hb : 0 < b) (β : ℝ) (k : ℕ) :
    (b ^ β) ^ k / b ^ ⌊(k : ℝ) * β⌋ = b ^ Int.fract ((k : ℝ) * β) := by
  have hfract : Int.fract ((k : ℝ) * β) = (k : ℝ) * β - (⌊(k : ℝ) * β⌋ : ℝ) :=
    (Int.self_sub_floor _).symm
  rw [hfract, Real.rpow_sub hb, Real.rpow_intCast, ← Real.rpow_mul_natCast hb.le β k,
    mul_comm β (k : ℝ)]

/-- Clearing the integral denominator from an arc identity. -/
private theorem eq_rpow_add_intCast_of_div_eq {b y t : ℝ} {n : ℤ} (hb : 0 < b)
    (h : y / b ^ n = b ^ t) : y = b ^ (t + (n : ℝ)) := by
  have hbn : b ^ n ≠ 0 := zpow_ne_zero n hb.ne'
  rw [Real.rpow_add hb, Real.rpow_intCast]
  exact (div_eq_iff hbn).mp h

/-- If `M = 2 ^ β` and `A = 3 ^ β`, then every synchronized orbit point lies on the compact
arc: the shared floor exponent `⌊k β⌋` is removed simultaneously from both coordinates,
leaving the common fractional part `{k β}` as the arc parameter. -/
theorem synchronizedOrbitPoint_mem_compactExponentialArc {M A : ℕ} {β : ℝ}
    (hM : (M : ℝ) = (2 : ℝ) ^ β) (hA : (A : ℝ) = (3 : ℝ) ^ β) (k : ℕ) :
    synchronizedOrbitPoint M A β k ∈ compactExponentialArc := by
  refine (mem_compactExponentialArc_synchronizedOrbitPoint M A β k).mpr
    ⟨Int.fract ((k : ℝ) * β), Int.fract_nonneg _, Int.fract_lt_one _, ?_, ?_⟩
  · rw [hM]
    exact rpow_pow_div_zpow_floor (by norm_num : (0 : ℝ) < 2) β k
  · rw [hA]
    exact rpow_pow_div_zpow_floor (by norm_num : (0 : ℝ) < 3) β k

/-- **Forward direction, canonical form.**  If the Alaoglu--Erdős conjecture fails, the
canonical primitive generator `β` is an irrational positive *least* noninteger solution, and
the two integers `M = 2 ^ β`, `A = 3 ^ β` exceed one and keep the whole synchronized orbit on
the compact arc. -/
theorem exists_canonical_compactOrbit_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ M A : ℕ, ∃ β : ℝ,
      1 < M ∧ 1 < A ∧ Irrational β ∧ 0 < β ∧
        IsLeastTwoBaseNonintegerSolution β ∧
        (2 : ℝ) ^ β = (M : ℝ) ∧ (3 : ℝ) ^ β = (A : ℝ) ∧
        ∀ k : ℕ, synchronizedOrbitPoint M A β k ∈ compactExponentialArc := by
  obtain ⟨w, d, a, c, β, _, _, _, _, _, _, _, _, _, _, h₂β, h₃β, hβirr, hβleast, _, _⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  have hβpos : 0 < β := hβleast.pos
  have hM1 : 1 < 2 ^ a * w ^ d := by
    have h1 : (1 : ℝ) < ((2 ^ a * w ^ d : ℕ) : ℝ) := by
      rw [← h₂β]
      exact Real.one_lt_rpow (by norm_num) hβpos
    exact_mod_cast h1
  have hA1 : 1 < c := by
    have h1 : (1 : ℝ) < (c : ℝ) := by
      rw [← h₃β]
      exact Real.one_lt_rpow (by norm_num) hβpos
    exact_mod_cast h1
  exact ⟨2 ^ a * w ^ d, c, β, hM1, hA1, hβirr, hβpos, hβleast, h₂β, h₃β,
    fun k ↦ synchronizedOrbitPoint_mem_compactExponentialArc h₂β.symm h₃β.symm k⟩

/-- **Converse direction.**  A synchronized compact orbit with an irrational parameter forces
the Alaoglu--Erdős conjecture to fail.  Neither `1 < M` nor `1 < A` nor `0 < β` is needed: arc
membership already pins `M = 2 ^ β` and `A = 3 ^ β`. -/
theorem not_alaogluErdosConjecture_of_compactOrbit {M A : ℕ} {β : ℝ}
    (hβirr : Irrational β)
    (horbit : ∀ k : ℕ, 1 ≤ k →
      synchronizedOrbitPoint M A β k ∈ compactExponentialArc) :
    ¬ AlaogluErdosConjecture := by
  -- Arc membership at index `k`, with the denominator cleared.
  have hstep : ∀ k : ℕ, 1 ≤ k → ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      (M : ℝ) ^ k = (2 : ℝ) ^ (t + (⌊(k : ℝ) * β⌋ : ℝ)) ∧
      (A : ℝ) ^ k = (3 : ℝ) ^ (t + (⌊(k : ℝ) * β⌋ : ℝ)) := by
    intro k hk
    obtain ⟨t, ht0, ht1, h2, h3⟩ :=
      (mem_compactExponentialArc_synchronizedOrbitPoint M A β k).mp (horbit k hk)
    exact ⟨t, ht0, ht1,
      eq_rpow_add_intCast_of_div_eq (by norm_num : (0 : ℝ) < 2) h2,
      eq_rpow_add_intCast_of_div_eq (by norm_num : (0 : ℝ) < 3) h3⟩
  -- The index `k = 1` produces a common exponent `γ` with `M = 2 ^ γ` and `A = 3 ^ γ`.
  obtain ⟨t₁, _, _, hMone, hAone⟩ := hstep 1 le_rfl
  rw [pow_one] at hMone hAone
  obtain ⟨γ, hMγ, hAγ⟩ :
      ∃ γ : ℝ, (M : ℝ) = (2 : ℝ) ^ γ ∧ (A : ℝ) = (3 : ℝ) ^ γ := ⟨_, hMone, hAone⟩
  -- Both `k γ` and `k β` lie in `[⌊k β⌋, ⌊k β⌋ + 1)`, so they differ by less than one.
  have hbound : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * |γ - β| < 1 := by
    intro k hk
    obtain ⟨t, ht0, ht1, hMk, _⟩ := hstep k hk
    have hpow : (2 : ℝ) ^ (γ * (k : ℝ)) =
        (2 : ℝ) ^ (t + (⌊(k : ℝ) * β⌋ : ℝ)) := by
      rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) γ k, ← hMγ]
      exact hMk
    have heq : γ * (k : ℝ) = t + (⌊(k : ℝ) * β⌋ : ℝ) :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective hpow
    have hfl : ((⌊(k : ℝ) * β⌋ : ℤ) : ℝ) ≤ (k : ℝ) * β := Int.floor_le _
    have hfl' : (k : ℝ) * β < ((⌊(k : ℝ) * β⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hkabs : (k : ℝ) * |γ - β| = |(γ - β) * (k : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
      ring
    have hprod : (γ - β) * (k : ℝ) = γ * (k : ℝ) - (k : ℝ) * β := by ring
    rw [hkabs, hprod, abs_lt]
    constructor <;> linarith
  -- Archimedean property: a real number of arbitrarily small multiples must vanish.
  have hγβ : γ = β := by
    by_contra hne
    have hpos : 0 < |γ - β| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |γ - β|)
    have hinvpos : (0 : ℝ) < 1 / |γ - β| := one_div_pos.mpr hpos
    have hn0 : (0 : ℝ) < (n : ℝ) := hinvpos.trans hn
    have hnpos : 0 < n := by exact_mod_cast hn0
    have hgt : 1 < (n : ℝ) * |γ - β| := by
      have hmul := mul_lt_mul_of_pos_right hn hpos
      rwa [one_div, inv_mul_cancel₀ hpos.ne'] at hmul
    have hlt := hbound n (by omega)
    linarith
  rw [hγβ] at hMγ hAγ
  intro hconj
  have h₂ : (2 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := ⟨(M : ℤ), by exact_mod_cast hMγ⟩
  have h₃ : (3 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := ⟨(A : ℤ), by exact_mod_cast hAγ⟩
  obtain ⟨z, hz⟩ := hconj h₂ h₃
  exact hβirr.ne_int z hz.symm

/-- **Compact-orbit reformulation.**  The Alaoglu--Erdős conjecture fails if and only if there
are integers `M, A > 1` and an irrational `β > 0` such that, for every `k ≥ 1`, the point
`(M ^ k / 2 ^ ⌊k β⌋, A ^ k / 3 ^ ⌊k β⌋)` lies on the compact arc
`𝒜 = {(2 ^ t, 3 ^ t) : 0 ≤ t < 1}`. -/
theorem not_alaogluErdosConjecture_iff_exists_compactOrbit :
    ¬ AlaogluErdosConjecture ↔
      ∃ M A : ℕ, ∃ β : ℝ,
        1 < M ∧ 1 < A ∧ Irrational β ∧ 0 < β ∧
          ∀ k : ℕ, 1 ≤ k →
            synchronizedOrbitPoint M A β k ∈ compactExponentialArc := by
  constructor
  · intro hfail
    obtain ⟨M, A, β, hM1, hA1, hβirr, hβpos, _, _, _, horbit⟩ :=
      exists_canonical_compactOrbit_of_not_alaogluErdosConjecture hfail
    exact ⟨M, A, β, hM1, hA1, hβirr, hβpos, fun k _ ↦ horbit k⟩
  · rintro ⟨M, A, β, _, _, hβirr, _, horbit⟩
    exact not_alaogluErdosConjecture_of_compactOrbit hβirr horbit

/-- Positive restatement of the compact-orbit reformulation: the conjecture holds exactly when
every candidate synchronized orbit leaves the compact arc at some index `k ≥ 1`. -/
theorem alaogluErdosConjecture_iff_no_compactOrbit :
    AlaogluErdosConjecture ↔
      ∀ M A : ℕ, ∀ β : ℝ, 1 < M → 1 < A → Irrational β → 0 < β →
        ∃ k : ℕ, 1 ≤ k ∧ synchronizedOrbitPoint M A β k ∉ compactExponentialArc := by
  constructor
  · intro hconj M A β hM hA hβirr hβpos
    by_contra hcon
    push_neg at hcon
    exact not_alaogluErdosConjecture_iff_exists_compactOrbit.mpr
      ⟨M, A, β, hM, hA, hβirr, hβpos, hcon⟩ hconj
  · intro h
    by_contra hfail
    obtain ⟨M, A, β, hM, hA, hβirr, hβpos, horbit⟩ :=
      not_alaogluErdosConjecture_iff_exists_compactOrbit.mp hfail
    obtain ⟨k, hk, hknot⟩ := h M A β hM hA hβirr hβpos
    exact hknot (horbit k hk)

end

end LeanProofs.TwoBaseIntegerExponent
