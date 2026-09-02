import FabiusFunction.ThueMorseAutocorrelation

/-!
# The limiting Thue–Morse autocorrelation at every shift

The atlas's `p1:thm:limiting-autocorrelation`: for every fixed shift `k`, the
normalized dyadic autocorrelation `η_m(k) = A_m(k) / 2^m` converges as
`m → ∞`, and the limit `η(k)` is characterized by

`η(0) = 1,  η(2r) = η(r),  η(2r+1) = -(η(r) + η(r+1)) / 2`.

`ThueMorseAutocorrelation` proves the exact finite recursions
`A_{m+1}(2r) = 2 A_m(r)` and `A_{m+1}(2r+1) = -(A_m(r) + A_m(r+1))`, and the
three closed-form limits `η(0) = 1`, `η(1) = η(2) = -1/3`.  What was open in
the corpus was existence at a *general* shift.  The point is that the
recursions are exact at every finite scale, so `η_{m+1}(2r) = η_m(r)` and
`η_{m+1}(2r+1) = -(η_m(r) + η_m(r+1))/2` hold on the nose; existence of
the limit then follows by strong induction on `k`, the only genuinely
analytic input being the two base cases `k = 0, 1` (the latter is the
contraction `η_{m+1}(1) = -(1 + η_m(1))/2`, already formal).

The limit is *defined* by the atlas's recursion (`limitingAutocorrelation`),
so the characterization is by construction and the theorem is the
convergence `tendsto_normalizedAutocorrelation`.

## Main declarations

* `normalizedAutocorrelation m k` — `η_m(k) = A_m(k) / 2^m`.
* `normalizedAutocorrelation_succ_even`, `_succ_odd` — the exact normalized
  recursions.
* `limitingAutocorrelation k` — `η(k)`, by the recursion, with
  `limitingAutocorrelation_two_mul`, `_two_mul_add_one` as its defining laws.
* `tendsto_normalizedAutocorrelation` — **`p1:eq:eta-limit-definition`**:
  `η_m(k) → η(k)` for every `k`.
-/

set_option autoImplicit false

namespace Fabius

open Filter Topology

/-- The normalized dyadic autocorrelation `η_m(k) = A_m(k) / 2^m`. -/
noncomputable def normalizedAutocorrelation (m k : ℕ) : ℝ :=
  (thueMorseAutocorrelation m k : ℝ) / 2 ^ m

/-- `η_{m+1}(2r) = η_m(r)`, exactly. -/
theorem normalizedAutocorrelation_succ_even (m r : ℕ) :
    normalizedAutocorrelation (m + 1) (2 * r) = normalizedAutocorrelation m r := by
  unfold normalizedAutocorrelation
  rw [thueMorseAutocorrelation_succ_even, pow_succ]
  push_cast
  have h : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-- `η_{m+1}(2r+1) = -(η_m(r) + η_m(r+1)) / 2`, exactly. -/
theorem normalizedAutocorrelation_succ_odd (m r : ℕ) :
    normalizedAutocorrelation (m + 1) (2 * r + 1)
      = -(normalizedAutocorrelation m r + normalizedAutocorrelation m (r + 1)) / 2 := by
  unfold normalizedAutocorrelation
  rw [thueMorseAutocorrelation_succ_odd, pow_succ]
  push_cast
  have h : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp
  ring

/-- The limiting autocorrelation `η(k)`, defined by the atlas's recursion
`η(0) = 1`, `η(1) = -1/3`, `η(2r) = η(r)`, `η(2r+1) = -(η(r) + η(r+1))/2`. -/
noncomputable def limitingAutocorrelation : ℕ → ℝ
  | 0 => 1
  | 1 => -1 / 3
  | k + 2 =>
      if h : k % 2 = 0 then limitingAutocorrelation (k / 2 + 1)
      else -(limitingAutocorrelation ((k + 1) / 2) + limitingAutocorrelation ((k + 1) / 2 + 1)) / 2
  decreasing_by all_goals omega

@[simp] theorem limitingAutocorrelation_zero : limitingAutocorrelation 0 = 1 := by
  rw [limitingAutocorrelation]

@[simp] theorem limitingAutocorrelation_one : limitingAutocorrelation 1 = -1 / 3 := by
  rw [limitingAutocorrelation]

/-- `η(2r) = η(r)`. -/
theorem limitingAutocorrelation_two_mul (r : ℕ) :
    limitingAutocorrelation (2 * r) = limitingAutocorrelation r := by
  rcases r with _ | r
  · rfl
  · rw [show 2 * (r + 1) = 2 * r + 2 by ring, limitingAutocorrelation, dif_pos (by omega)]
    congr 1
    omega

/-- `η(2r+1) = -(η(r) + η(r+1)) / 2`. -/
theorem limitingAutocorrelation_two_mul_add_one (r : ℕ) :
    limitingAutocorrelation (2 * r + 1)
      = -(limitingAutocorrelation r + limitingAutocorrelation (r + 1)) / 2 := by
  rcases r with _ | r
  · simp only [mul_zero, zero_add, limitingAutocorrelation_zero, limitingAutocorrelation_one]
    norm_num
  · rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by ring, limitingAutocorrelation,
      dif_neg (by omega)]
    have e1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    rw [e1]

/-- **Existence of the limiting autocorrelation at every shift**
(`p1:eq:eta-limit-definition`): `η_m(k) → η(k)` as `m → ∞`, for every `k`. -/
theorem tendsto_normalizedAutocorrelation (k : ℕ) :
    Tendsto (fun m : ℕ => normalizedAutocorrelation m k) atTop
      (𝓝 (limitingAutocorrelation k)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simpa [normalizedAutocorrelation] using tendsto_thueMorseAutocorrelation_zero_shift
    · simpa [normalizedAutocorrelation] using tendsto_thueMorseAutocorrelation_one
    · rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
      · -- `k + 2 = 2 (r + 1)`
        have hk : k + 2 = 2 * (r + 1) := by omega
        have h := ih (r + 1) (by omega)
        have h2 : Tendsto (fun m : ℕ => normalizedAutocorrelation (m + 1) (k + 2)) atTop
            (𝓝 (limitingAutocorrelation (r + 1))) := by
          simp_rw [hk, normalizedAutocorrelation_succ_even]
          exact h
        rw [hk, limitingAutocorrelation_two_mul]
        rw [hk] at h2
        exact (tendsto_add_atTop_iff_nat 1).mp h2
      · -- `k + 2 = 2 (r + 1) + 1`
        have hk : k + 2 = 2 * (r + 1) + 1 := by omega
        have h1 := ih (r + 1) (by omega)
        have h2 := ih (r + 1 + 1) (by omega)
        have h3 : Tendsto (fun m : ℕ => normalizedAutocorrelation (m + 1) (k + 2)) atTop
            (𝓝 (-(limitingAutocorrelation (r + 1) + limitingAutocorrelation (r + 1 + 1)) / 2)) := by
          simp_rw [hk, normalizedAutocorrelation_succ_odd]
          exact ((h1.add h2).neg).div_const 2
        rw [hk, limitingAutocorrelation_two_mul_add_one]
        rw [hk] at h3
        exact (tendsto_add_atTop_iff_nat 1).mp h3

end Fabius
