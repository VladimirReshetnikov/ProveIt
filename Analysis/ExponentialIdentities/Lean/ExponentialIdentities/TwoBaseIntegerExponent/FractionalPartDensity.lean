import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Fractional-part density dichotomy for two-base solutions

The set of real solutions of the simultaneous integrality conditions `2 ^ x ∈ ℤ` and
`3 ^ x ∈ ℤ` is an additive monoid containing every natural number.  Consequently a single
nonintegral solution `x` produces the infinite family `k * x` of further nonintegral
solutions, and since `x` is necessarily irrational, the fractional parts of these multiples
are dense in the unit interval.

This yields a sharp dichotomy: **either the Alaoglu--Erdős conjecture holds, or the
fractional parts of nonintegral solutions are dense in `[0, 1]`.**  In particular the full
conjecture is *equivalent* to each of the following ostensibly much weaker statements:

* some nonempty open subinterval of `(0, 1)` is free of fractional parts of nonintegral
  solutions;
* the fractional parts of nonintegral solutions are bounded away from `1`;
* the fractional parts of nonintegral solutions are bounded away from `0`.

Thus no nontrivial upper (or lower) bound on the fractional part of a hypothetical
counterexample can be established short of the conjecture itself, while conversely any such
bound would already close the problem.  The density mechanism is quantitative: it only uses
Dirichlet's approximation theorem, so every step is effective.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-!
### Density of fractional parts of positive natural multiples of an irrational number

Mathlib provides density of the *integer* orbit on the additive circle.  The results below
give the positive-natural-multiple refinement in terms of `Int.fract`, which is the form
needed here: only positive multiples of a solution are again solutions.
-/

/-- The fractional part of an irrational number is irrational. -/
private theorem irrational_fract {α : ℝ} (hα : Irrational α) : Irrational (Int.fract α) := by
  have h := hα.sub_intCast ⌊α⌋
  rwa [Int.self_sub_floor] at h

/-- An irrational number has strictly positive fractional part. -/
private theorem fract_pos_of_irrational {α : ℝ} (hα : Irrational α) : 0 < Int.fract α := by
  rcases (Int.fract_nonneg α).lt_or_eq with h | h
  · exact h
  · exact absurd (by simpa using (irrational_fract hα).ne_int 0) (not_not.mpr h.symm)

/-- Multiplying out the integer part: the fractional part of `k * α` equals the fractional
part of `k * Int.fract α`. -/
private theorem fract_nat_mul_eq_fract_nat_mul_fract (α : ℝ) (k : ℕ) :
    Int.fract ((k : ℝ) * α) = Int.fract ((k : ℝ) * Int.fract α) := by
  have h : (k : ℝ) * α = (k : ℝ) * Int.fract α + ((k * ⌊α⌋ : ℤ) : ℝ) := by
    push_cast
    rw [Int.fract]
    ring
  rw [h, Int.fract_add_intCast]

/-- Dirichlet's theorem in fractional-part form: for irrational `ξ` and `δ > 0` some
positive natural multiple of `ξ` has fractional part within `δ` of the endpoints of the
unit interval. -/
private theorem exists_pos_nat_fract_near_end {ξ : ℝ} (hξ : Irrational ξ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧
      (Int.fract ((q : ℝ) * ξ) < δ ∨ 1 - δ < Int.fract ((q : ℝ) * ξ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h0 : (0 : ℝ) < 1 / δ := by positivity
      simp at hn
      linarith
    · exact h
  obtain ⟨j, k, hk0, _hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le ξ hnpos
  have hsmall : |(k : ℝ) * ξ - j| < δ := by
    refine hjk.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have h1δ : 1 / δ < n := hn
    rw [div_lt_iff₀ hδ] at h1δ
    nlinarith
  lift k to ℕ using hk0.le with q hq
  push_cast at hsmall hjk
  have hqpos : 0 < q := by exact_mod_cast hk0
  -- A `δ`-independent localization: the multiple is within `1/2` of the integer `j`.
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hhalf : -(1 / 2 : ℝ) ≤ (q : ℝ) * ξ - j ∧ ((q : ℝ) * ξ - j : ℝ) ≤ 1 / 2 := by
    have hbound : |(q : ℝ) * ξ - j| ≤ 1 / 2 := by
      refine hjk.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact abs_le.mp hbound
  refine ⟨q, hqpos, ?_⟩
  have hirr : Irrational ((q : ℝ) * ξ) := hξ.natCast_mul hqpos.ne'
  have hne : (q : ℝ) * ξ ≠ (j : ℝ) := hirr.ne_int j
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `q * ξ` is just below the integer `j`; its fractional part is close to `1`.
    right
    have h1 : (j : ℝ) - (q : ℝ) * ξ < δ := by
      have := abs_lt.mp hsmall
      linarith [this.1]
    have hfr : Int.fract ((q : ℝ) * ξ) = (q : ℝ) * ξ - j + 1 := by
      have hval : Int.fract ((q : ℝ) * ξ) = Int.fract ((q : ℝ) * ξ - j + 1) := by
        rw [show (q : ℝ) * ξ - j + 1 = (q : ℝ) * ξ + ((1 - j : ℤ) : ℝ) by push_cast; ring,
          Int.fract_add_intCast]
      rw [hval, Int.fract_eq_self.mpr ⟨by linarith [hhalf.1], by linarith⟩]
    rw [hfr]
    linarith
  · -- `q * ξ` is just above the integer `j`; its fractional part is close to `0`.
    left
    have h1 : (q : ℝ) * ξ - j < δ := by
      have := abs_lt.mp hsmall
      linarith [this.2]
    have hfr : Int.fract ((q : ℝ) * ξ) = (q : ℝ) * ξ - j := by
      have hval : Int.fract ((q : ℝ) * ξ) = Int.fract ((q : ℝ) * ξ - j) := by
        rw [show (q : ℝ) * ξ - j = (q : ℝ) * ξ + ((-j : ℤ) : ℝ) by push_cast; ring,
          Int.fract_add_intCast]
      rw [hval, Int.fract_eq_self.mpr ⟨by linarith, by linarith [hhalf.2]⟩]
    rw [hfr]
    linarith

/-- Stepping lemma, ascending case: if `Int.fract α` is a small positive step then suitable
positive multiples of `α` land within that step of any target in `[0, 1)`. -/
private theorem exists_nat_fract_close_of_fract_lt {α : ℝ} (hα : Irrational α)
    {δ t : ℝ} (hβδ : Int.fract α < δ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ k : ℕ, 0 < k ∧ |Int.fract ((k : ℝ) * α) - t| < δ := by
  set β := Int.fract α with hβ
  have hβpos : 0 < β := fract_pos_of_irrational hα
  have hβlt : β < 1 := Int.fract_lt_one α
  rcases lt_or_ge t β with hlt | hge
  · -- One step suffices.
    refine ⟨1, one_pos, ?_⟩
    rw [fract_nat_mul_eq_fract_nat_mul_fract, ← hβ]
    rw [show ((1 : ℕ) : ℝ) * β = β by norm_num, Int.fract_eq_self.mpr ⟨hβpos.le, hβlt⟩]
    rw [abs_lt]
    constructor <;> nlinarith
  · -- Walk up to the target with steps of size `β`.
    set k := ⌊t / β⌋₊ with hk
    have hk1 : 1 ≤ k := Nat.le_floor (by rw [le_div_iff₀ hβpos]; simpa using hge)
    have hkβ_le : (k : ℝ) * β ≤ t := by
      have h := Nat.floor_le (div_nonneg ht0 hβpos.le)
      rw [← hk] at h
      calc (k : ℝ) * β ≤ t / β * β := mul_le_mul_of_nonneg_right h hβpos.le
        _ = t := div_mul_cancel₀ t hβpos.ne'
    have hkβ_gt : t - β < (k : ℝ) * β := by
      have h := Nat.lt_floor_add_one (t / β)
      rw [← hk] at h
      have := (div_lt_iff₀ hβpos).mp h
      nlinarith
    refine ⟨k, hk1, ?_⟩
    rw [fract_nat_mul_eq_fract_nat_mul_fract, ← hβ,
      Int.fract_eq_self.mpr ⟨mul_nonneg (Nat.cast_nonneg k) hβpos.le, by linarith⟩]
    rw [abs_lt]
    constructor <;> nlinarith
/-- Stepping lemma, descending case: if `Int.fract α` is within a small step below `1` then
suitable positive multiples of `α` land within that step of any target in `[0, 1)`. -/
private theorem exists_nat_fract_close_of_lt_fract {α : ℝ} (hα : Irrational α)
    {δ t : ℝ} (hβδ : 1 - δ < Int.fract α) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ k : ℕ, 0 < k ∧ |Int.fract ((k : ℝ) * α) - t| < δ := by
  set γ := 1 - Int.fract α with hγ
  have hγpos : 0 < γ := by
    have := Int.fract_lt_one α
    simp only [hγ]
    linarith
  have hγδ : γ < δ := by simp only [hγ]; linarith
  have hγirr : Irrational γ := by
    have h := (irrational_fract hα).natCast_sub 1
    simpa using h
  -- For `k * γ < 1` the fractional part of `k * α` is `1 - k * γ`.
  have key : ∀ k : ℕ, 0 < k → (k : ℝ) * γ < 1 →
      Int.fract ((k : ℝ) * α) = 1 - (k : ℝ) * γ := by
    intro k hkpos hkγ
    have hkγpos : 0 < (k : ℝ) * γ := by positivity
    have hkγirr : Irrational ((k : ℝ) * γ) := hγirr.natCast_mul hkpos.ne'
    have h1 : Int.fract ((k : ℝ) * α) = Int.fract (-((k : ℝ) * γ)) := by
      rw [fract_nat_mul_eq_fract_nat_mul_fract]
      have hval : (k : ℝ) * Int.fract α = -((k : ℝ) * γ) + ((k : ℤ) : ℝ) := by
        simp only [hγ]
        push_cast
        ring
      rw [hval, Int.fract_add_intCast]
    have h2 : Int.fract ((k : ℝ) * γ) = (k : ℝ) * γ :=
      Int.fract_eq_self.mpr ⟨hkγpos.le, hkγ⟩
    have h3 : Int.fract ((k : ℝ) * γ) ≠ 0 := by
      rw [h2]
      exact hkγpos.ne'
    rw [h1, Int.fract_neg h3, h2]
  set s := 1 - t with hs
  have hspos : 0 < s := by simp only [hs]; linarith
  have hsle : s ≤ 1 := by simp only [hs]; linarith
  rcases lt_or_ge s γ with hlt | hge
  · -- One step suffices.
    refine ⟨1, one_pos, ?_⟩
    have hγ1 : (1 : ℝ) * γ < 1 := by
      have hne : γ ≠ 1 := by simpa using hγirr.ne_int 1
      have hγle : γ ≤ 1 := by
        have := Int.fract_nonneg α
        simp only [hγ]
        linarith
      rw [one_mul]
      exact lt_of_le_of_ne hγle hne
    rw [key 1 one_pos (by simpa using hγ1)]
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  · -- Walk down from `1` with steps of size `γ`.
    set k := ⌊s / γ⌋₊ with hk
    have hk1 : 1 ≤ k := Nat.le_floor (by rw [le_div_iff₀ hγpos]; simpa using hge)
    have hkγ_le : (k : ℝ) * γ ≤ s := by
      have h := Nat.floor_le (div_nonneg hspos.le hγpos.le)
      rw [← hk] at h
      calc (k : ℝ) * γ ≤ s / γ * γ := mul_le_mul_of_nonneg_right h hγpos.le
        _ = s := div_mul_cancel₀ s hγpos.ne'
    have hkγ_gt : s - γ < (k : ℝ) * γ := by
      have h := Nat.lt_floor_add_one (s / γ)
      rw [← hk] at h
      have := (div_lt_iff₀ hγpos).mp h
      nlinarith
    have hkγlt : (k : ℝ) * γ < 1 := by
      have hkγirr : Irrational ((k : ℝ) * γ) := hγirr.natCast_mul (by omega)
      have hne : (k : ℝ) * γ ≠ 1 := by simpa using hkγirr.ne_int 1
      exact lt_of_le_of_ne (hkγ_le.trans hsle) hne
    refine ⟨k, hk1, ?_⟩
    rw [key k hk1 hkγlt, abs_lt]
    constructor <;> nlinarith

/-- **Density of fractional parts of positive natural multiples of an irrational number.**
For irrational `ξ`, every point of `[0, 1]` is approximated within any `ε > 0` by the
fractional part of a positive natural multiple of `ξ`. -/
theorem exists_pos_nat_fract_close_of_irrational {ξ : ℝ} (hξ : Irrational ξ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ |Int.fract ((k : ℝ) * ξ) - t| < ε := by
  obtain ⟨ht0, ht1⟩ := ht
  set δ := min (ε / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := by
    apply lt_min <;> positivity
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  set t' := min t (1 - δ) with ht'def
  have ht'0 : 0 ≤ t' := le_min ht0 (by linarith)
  have ht'1 : t' < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have htt' : |t' - t| ≤ δ := by
    rw [ht'def]
    rcases le_or_gt t (1 - δ) with h | h
    · rw [min_eq_left h]
      simpa using hδpos.le
    · rw [min_eq_right h.le, abs_le]
      constructor <;> nlinarith
  obtain ⟨q, hq0, hcase⟩ := exists_pos_nat_fract_near_end hξ hδpos
  set α := (q : ℝ) * ξ with hα
  have hαirr : Irrational α := hξ.natCast_mul hq0.ne'
  have main : ∃ k : ℕ, 0 < k ∧ |Int.fract ((k : ℝ) * α) - t'| < δ := by
    rcases hcase with h | h
    · exact exists_nat_fract_close_of_fract_lt hαirr h ht'0 ht'1
    · exact exists_nat_fract_close_of_lt_fract hαirr h ht'0 ht'1
  obtain ⟨k, hk0, hkclose⟩ := main
  refine ⟨k * q, Nat.mul_pos hk0 hq0, ?_⟩
  have hrw : ((k * q : ℕ) : ℝ) * ξ = (k : ℝ) * α := by
    simp only [hα]
    push_cast
    ring
  rw [hrw]
  calc |Int.fract ((k : ℝ) * α) - t|
      ≤ |Int.fract ((k : ℝ) * α) - t'| + |t' - t| := by
        have := abs_sub_le (Int.fract ((k : ℝ) * α)) t' t
        simpa using this
    _ < δ + δ := add_lt_add_of_lt_of_le hkclose htt'
    _ ≤ ε := by linarith

/-!
### The two-base solution monoid
-/

/-- Integral powers at a positive base are closed under addition of exponents: the set of
solutions is an additive monoid. -/
theorem rpow_integer_add {b : ℝ} (hb : 0 < b) {x y : ℝ}
    (hx : b ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hy : b ^ y ∈ Set.range ((↑) : ℤ → ℝ)) :
    b ^ (x + y) ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  refine ⟨z * w, ?_⟩
  rw [Real.rpow_add hb]
  push_cast
  rw [hz, hw]

/-- A positive natural multiple of a nonintegral two-base solution is again a nonintegral
two-base solution. -/
theorem noninteger_solution_nat_mul {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) {k : ℕ} (hk : 0 < k) :
    (2 : ℝ) ^ ((k : ℝ) * x) ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ ((k : ℝ) * x) ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (k : ℝ) * x ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hxirr : Irrational x := irrational_of_not_integer_of_two_rpow_integer hx h₂
  refine ⟨?_, ?_, ?_⟩
  · simpa using rpow_integer_nat_mul (b := 2) h₂ k
  · simpa using rpow_integer_nat_mul (b := 3) h₃ k
  · rintro ⟨z, hz⟩
    exact (hxirr.natCast_mul hk.ne').ne_int z hz.symm

/-!
### The dichotomy and its consequences
-/

/-- **Density dichotomy.**  If a single nonintegral two-base solution exists, then the
fractional parts of nonintegral two-base solutions are dense in the unit interval. -/
theorem dense_fract_of_noninteger_solution {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ,
      (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) ∧
      y ∉ Set.range ((↑) : ℤ → ℝ) ∧
      |Int.fract y - t| < ε := by
  have hxirr : Irrational x := irrational_of_not_integer_of_two_rpow_integer hx h₂
  obtain ⟨k, hk0, hkclose⟩ := exists_pos_nat_fract_close_of_irrational hxirr ht hε
  obtain ⟨hy₂, hy₃, hyni⟩ := noninteger_solution_nat_mul h₂ h₃ hx hk0
  exact ⟨(k : ℝ) * x, hy₂, hy₃, hyni, hkclose⟩

/-- **Zero-free-interval equivalence.**  The Alaoglu--Erdős conjecture is equivalent to the
existence of a single nonempty open subinterval of `(0, 1)` avoided by the fractional parts
of all nonintegral solutions.  Establishing any such gap, however small, would settle the
full conjecture. -/
theorem alaogluErdosConjecture_iff_fract_avoids_interval :
    AlaogluErdosConjecture ↔
      ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
        ∀ y : ℝ,
          (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          y ∉ Set.range ((↑) : ℤ → ℝ) →
          Int.fract y ∉ Set.Ioo u v := by
  constructor
  · intro h
    exact ⟨0, 1, le_refl 0, one_pos, le_refl 1,
      fun y hy₂ hy₃ hyni _ ↦ hyni (h hy₂ hy₃)⟩
  · rintro ⟨u, v, hu0, huv, hv1, havoid⟩ x h₂ h₃
    by_contra hx
    have ht : (u + v) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hε : 0 < (v - u) / 2 := by linarith
    obtain ⟨y, hy₂, hy₃, hyni, hyclose⟩ :=
      dense_fract_of_noninteger_solution h₂ h₃ hx ht hε
    refine havoid y hy₂ hy₃ hyni ?_
    rw [abs_lt] at hyclose
    exact ⟨by linarith [hyclose.1], by linarith [hyclose.2]⟩

/-- **Upper-gap equivalence.**  The conjecture is equivalent to the fractional parts of
nonintegral solutions being bounded away from `1`. -/
theorem alaogluErdosConjecture_iff_fract_bounded_away_one :
    AlaogluErdosConjecture ↔
      ∃ c : ℝ, c < 1 ∧
        ∀ y : ℝ,
          (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          y ∉ Set.range ((↑) : ℤ → ℝ) →
          Int.fract y ≤ c := by
  constructor
  · intro h
    exact ⟨0, one_pos, fun y hy₂ hy₃ hyni ↦ absurd (h hy₂ hy₃) hyni⟩
  · rintro ⟨c, hc1, hbound⟩
    rw [alaogluErdosConjecture_iff_fract_avoids_interval]
    refine ⟨max c 0, 1, le_max_right _ _, ?_, le_refl 1, ?_⟩
    · exact max_lt hc1 one_pos
    · intro y hy₂ hy₃ hyni hmem
      exact absurd (hbound y hy₂ hy₃ hyni)
        (not_le.mpr (lt_of_le_of_lt (le_max_left c 0) hmem.1))

/-- **Lower-gap equivalence.**  The conjecture is equivalent to the fractional parts of
nonintegral solutions being bounded away from `0`. -/
theorem alaogluErdosConjecture_iff_fract_bounded_away_zero :
    AlaogluErdosConjecture ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ y : ℝ,
          (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) →
          y ∉ Set.range ((↑) : ℤ → ℝ) →
          c ≤ Int.fract y := by
  constructor
  · intro h
    exact ⟨1, one_pos, fun y hy₂ hy₃ hyni ↦ absurd (h hy₂ hy₃) hyni⟩
  · rintro ⟨c, hc0, hbound⟩
    rw [alaogluErdosConjecture_iff_fract_avoids_interval]
    refine ⟨0, min c 1, le_refl 0, lt_min hc0 one_pos, min_le_right _ _, ?_⟩
    intro y hy₂ hy₃ hyni hmem
    exact absurd (hbound y hy₂ hy₃ hyni)
      (not_le.mpr (lt_of_lt_of_le hmem.2 (min_le_left c 1)))

/-- If a nonintegral two-base solution exists at all, then infinitely many exist. -/
theorem infinite_noninteger_solutions_of_exists {x : ℝ}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    {y : ℝ |
      (2 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ y ∈ Set.range ((↑) : ℤ → ℝ) ∧
      y ∉ Set.range ((↑) : ℤ → ℝ)}.Infinite := by
  have hxpos : 0 < x := by
    rcases (IntegerExponent.nonneg_of_two_rpow_integer h₂).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by simp [← h]⟩ hx
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * x) ?_ ?_
  · intro a b hab
    have : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) :=
      mul_right_cancel₀ hxpos.ne' hab
    exact_mod_cast Nat.succ_injective (by exact_mod_cast this)
  · intro k
    obtain ⟨hy₂, hy₃, hyni⟩ :=
      noninteger_solution_nat_mul h₂ h₃ hx (k := k + 1) k.succ_pos
    exact ⟨hy₂, hy₃, hyni⟩

end LeanProofs.TwoBaseIntegerExponent
