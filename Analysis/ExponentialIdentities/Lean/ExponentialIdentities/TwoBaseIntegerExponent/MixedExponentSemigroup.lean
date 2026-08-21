import ExponentialIdentities.TwoBaseIntegerExponent.MultiplicativeRank

/-!
# The mixed exponent semigroup `ℕ + ℕ θ`

Write `θ = log 3 / log 2` (`logThreeDivLogTwo`).  A *two-base natural candidate* is a
positive natural number `m` with `m ^ θ ∈ ℤ`; equivalently, `x = log₂ m` is a real number
with `2 ^ x` and `3 ^ x` both rational integers.

This module records the observation that a candidate carries far more integral data than the
single value `m ^ θ`.  Indeed, if `m ^ θ = n ∈ ℕ`, then for **every** pair `(a, b)` of
natural numbers
`m ^ (a + b * θ) = m ^ a * (m ^ θ) ^ b = m ^ a * n ^ b ∈ ℕ`,
which is equation `eq:mixed-integrality` of the report
`alaoglu-erdos-further-report.tex`, Section "New result II".  The exponents available to a
candidate therefore form the additive semigroup
`Λ_θ = {a + b * θ : a, b ∈ ℕ} ⊆ [0, ∞)`,
a two-dimensional lattice cone rather than the one-dimensional set `{0, 1, 2, …}` used by
the ordinary Vandermonde constructions.

The contents are:

* `mixedExponent`, the pair-indexed exponent `(a, b) ↦ a + b * θ`, together with its
  additive structure (`mixedExponent_add`) and its packaging as an `AddSubmonoid ℝ`
  (`mixedExponentSemigroup`);
* `mixedExponent_injective`: distinct pairs give distinct exponents.  This is exactly where
  the irrationality of `θ` enters, via `irrational_logThreeDivLogTwo`, and it is what makes
  the exponent set genuinely two-dimensional;
* `candidateRpowNat`, the natural number `m ^ θ` attached to a candidate `m`, and the key
  integrality statement `exists_nat_rpow_mixedExponent`: for a candidate `m` and any
  `a b : ℕ`, the real number `m ^ (a + b * θ)` is a natural number, explicitly
  `m ^ a * (m ^ θ) ^ b`;
* order information: `mixedExponent` is strictly monotone in each coordinate, and, using the
  elementary enclosure `1 < θ < 8/5 < 2` already available in the base module, every
  exponent coming from the square box `[0, q]²` satisfies `a + b * θ ≤ 3 * q`.  The last
  bound is the combinatorial input to the report's square-box counting lemma.

Nothing here needs the analytic positivity of generalized Vandermonde determinants; that is
a separate development.  This module is the foundational layer consumed by
`SemigroupDeterminant.lean`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-! ### The pair-indexed exponent -/

/-- The **mixed exponent** attached to a pair of natural numbers: `(a, b) ↦ a + b * θ`,
where `θ = log 3 / log 2`.  Its range is the additive semigroup `Λ_θ` of exponents at which
every two-base natural candidate takes integral values. -/
def mixedExponent (ab : ℕ × ℕ) : ℝ := (ab.1 : ℝ) + (ab.2 : ℝ) * logThreeDivLogTwo

@[simp] theorem mixedExponent_mk (a b : ℕ) :
    mixedExponent (a, b) = (a : ℝ) + (b : ℝ) * logThreeDivLogTwo := rfl

/-- The mixed exponent of `(0, 0)` is `0`. -/
theorem mixedExponent_zero : mixedExponent (0, 0) = 0 := by
  simp [mixedExponent_mk]

/-- The mixed exponent of `(1, 0)` is `1`. -/
theorem mixedExponent_one_zero : mixedExponent (1, 0) = 1 := by
  simp [mixedExponent_mk]

/-- The mixed exponent of `(0, 1)` is `θ`. -/
theorem mixedExponent_zero_one : mixedExponent (0, 1) = logThreeDivLogTwo := by
  simp [mixedExponent_mk]

/-- **The semigroup law.**  `Λ_θ` is closed under addition: mixed exponents add
coordinatewise. -/
theorem mixedExponent_add (a b a' b' : ℕ) :
    mixedExponent (a + a', b + b') = mixedExponent (a, b) + mixedExponent (a', b') := by
  simp only [mixedExponent_mk]
  push_cast
  ring

/-! ### Positivity of `θ` and nonnegativity of the exponents -/

/-- The exponent `θ = log 3 / log 2` is positive; it is in fact larger than `1`. -/
theorem logThreeDivLogTwo_pos : 0 < logThreeDivLogTwo :=
  lt_trans zero_lt_one one_lt_logThreeDivLogTwo

/-- Every mixed exponent is nonnegative, so `Λ_θ ⊆ [0, ∞)`. -/
theorem mixedExponent_nonneg (ab : ℕ × ℕ) : 0 ≤ mixedExponent ab := by
  obtain ⟨a, b⟩ := ab
  simp only [mixedExponent_mk]
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hmul : (0 : ℝ) ≤ (b : ℝ) * logThreeDivLogTwo :=
    mul_nonneg hb logThreeDivLogTwo_pos.le
  linarith

/-! ### Injectivity: distinct pairs give distinct exponents -/

/-- **Distinctness of mixed exponents.**  Because `θ` is irrational, the map
`(a, b) ↦ a + b * θ` is injective on `ℕ × ℕ`, so the exponent semigroup `Λ_θ` is a faithful
copy of the lattice cone `ℕ × ℕ`. -/
theorem mixedExponent_injective : Function.Injective mixedExponent := by
  intro p q hpq
  exact IntegerExponent.Irrational.injective_nat_add_mul irrational_logThreeDivLogTwo hpq

/-- Distinct exponent pairs have distinct mixed exponents. -/
theorem mixedExponent_ne_of_ne {p q : ℕ × ℕ} (h : p ≠ q) :
    mixedExponent p ≠ mixedExponent q := fun he => h (mixedExponent_injective he)

/-- `mixedExponent` is injective on any set of pairs. -/
theorem mixedExponent_injOn (s : Set (ℕ × ℕ)) : Set.InjOn mixedExponent s :=
  Set.injOn_of_injective mixedExponent_injective

/-- A finite set of `k` exponent pairs produces exactly `k` distinct real exponents.  In
particular the `(q + 1) ^ 2` pairs of the square box `[0, q]²` give `(q + 1) ^ 2` distinct
mixed exponents. -/
theorem card_image_mixedExponent (s : Finset (ℕ × ℕ)) :
    (s.image mixedExponent).card = s.card :=
  Finset.card_image_of_injective s mixedExponent_injective

/-! ### Mixed integrality for natural candidates -/

/-- For a two-base natural candidate `m`, the real number `m ^ θ` is not merely a rational
integer but a **natural** number: it is positive because `m` is. -/
theorem exists_nat_rpow_logThreeDivLogTwo {m : ℕ} (hm : TwoBaseNaturalCandidate m) :
    ∃ n : ℕ, (n : ℝ) = (m : ℝ) ^ logThreeDivLogTwo := by
  obtain ⟨z, hz⟩ := hm.2
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
  have hpos : (0 : ℝ) < (m : ℝ) ^ logThreeDivLogTwo := Real.rpow_pos_of_pos hmR _
  have hzpos : (0 : ℝ) < (z : ℝ) := by rw [hz]; exact hpos
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast hzpos.le
  refine ⟨z.toNat, ?_⟩
  rw [← hz]
  exact_mod_cast Int.toNat_of_nonneg hz0

/-- The natural number `m ^ θ` attached to a number `m`.  It is only meaningful when `m` is a
two-base natural candidate, in which case `candidateRpowNat_cast` identifies its real image
with `m ^ θ`; the floor is a convenient total definition. -/
def candidateRpowNat (m : ℕ) : ℕ := ⌊(m : ℝ) ^ logThreeDivLogTwo⌋₊

/-- For a natural candidate `m`, the natural number `candidateRpowNat m` really is `m ^ θ`. -/
theorem candidateRpowNat_cast {m : ℕ} (hm : TwoBaseNaturalCandidate m) :
    (candidateRpowNat m : ℝ) = (m : ℝ) ^ logThreeDivLogTwo := by
  obtain ⟨n, hn⟩ := exists_nat_rpow_logThreeDivLogTwo hm
  have hfloor : candidateRpowNat m = n := by
    rw [candidateRpowNat, ← hn, Nat.floor_natCast]
  rw [hfloor, hn]

/-- For a natural candidate `m`, the natural number `m ^ θ` is positive. -/
theorem candidateRpowNat_pos {m : ℕ} (hm : TwoBaseNaturalCandidate m) :
    0 < candidateRpowNat m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
  have h : (0 : ℝ) < (candidateRpowNat m : ℝ) := by
    rw [candidateRpowNat_cast hm]
    exact Real.rpow_pos_of_pos hmR _
  exact_mod_cast h

/-- **The exponent split.**  For any positive natural `m`,
`m ^ (a + b * θ) = m ^ a * (m ^ θ) ^ b`,
where the outer powers on the right are ordinary monoid powers.  This is the real-analytic
half of `eq:mixed-integrality`; no candidate hypothesis is needed. -/
theorem rpow_mixedExponent_eq {m : ℕ} (hm : 0 < m) (a b : ℕ) :
    (m : ℝ) ^ mixedExponent (a, b) = (m : ℝ) ^ a * ((m : ℝ) ^ logThreeDivLogTwo) ^ b := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [mixedExponent_mk, Real.rpow_add hmR, Real.rpow_natCast,
    mul_comm (b : ℝ) logThreeDivLogTwo, Real.rpow_mul hmR.le, Real.rpow_natCast]

/-- **Mixed integrality with the explicit witness.**  For a natural candidate `m`, the real
number `m ^ (a + b * θ)` is the natural number `m ^ a * (m ^ θ) ^ b`.  This is exactly
equation `eq:mixed-integrality` of the report. -/
theorem cast_pow_mul_pow_eq_rpow_mixedExponent {m : ℕ} (hm : TwoBaseNaturalCandidate m)
    (a b : ℕ) :
    ((m ^ a * candidateRpowNat m ^ b : ℕ) : ℝ) = (m : ℝ) ^ mixedExponent (a, b) := by
  rw [rpow_mixedExponent_eq hm.1, ← candidateRpowNat_cast hm]
  push_cast
  ring

/-- **The key theorem.**  Every mixed exponent of a two-base natural candidate produces a
natural value: for a candidate `m` and any `a b : ℕ` there is `n : ℕ` with
`n = m ^ (a + b * θ)`.  The witness supplied is `m ^ a * (m ^ θ) ^ b`. -/
theorem exists_nat_rpow_mixedExponent {m : ℕ} (hm : TwoBaseNaturalCandidate m) (a b : ℕ) :
    ∃ n : ℕ, (n : ℝ) = (m : ℝ) ^ mixedExponent (a, b) :=
  ⟨m ^ a * candidateRpowNat m ^ b, cast_pow_mul_pow_eq_rpow_mixedExponent hm a b⟩

/-- The natural number produced by mixed integrality is positive. -/
theorem exists_pos_nat_rpow_mixedExponent {m : ℕ} (hm : TwoBaseNaturalCandidate m)
    (a b : ℕ) : ∃ n : ℕ, 0 < n ∧ (n : ℝ) = (m : ℝ) ^ mixedExponent (a, b) :=
  ⟨m ^ a * candidateRpowNat m ^ b,
    mul_pos (pow_pos hm.1 a) (pow_pos (candidateRpowNat_pos hm) b),
    cast_pow_mul_pow_eq_rpow_mixedExponent hm a b⟩

/-- Mixed integrality in the repository's usual `Set.range ((↑) : ℤ → ℝ)` form. -/
theorem rpow_mixedExponent_mem_range_int {m : ℕ} (hm : TwoBaseNaturalCandidate m) (a b : ℕ) :
    (m : ℝ) ^ mixedExponent (a, b) ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_rpow_mixedExponent hm a b
  exact ⟨(n : ℤ), by exact_mod_cast hn⟩

/-! ### The exponent semigroup as an additive submonoid of `ℝ` -/

/-- The **mixed exponent semigroup** `Λ_θ = {a + b * θ : a, b ∈ ℕ}`, as an additive submonoid
of `ℝ`.  Its elements are precisely the exponents at which every two-base natural candidate
takes natural values. -/
def mixedExponentSemigroup : AddSubmonoid ℝ where
  carrier := Set.range mixedExponent
  zero_mem' := ⟨(0, 0), mixedExponent_zero⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    obtain ⟨⟨a', b'⟩, rfl⟩ := hy
    exact ⟨(a + a', b + b'), mixedExponent_add a b a' b'⟩

@[simp] theorem mem_mixedExponentSemigroup_iff {t : ℝ} :
    t ∈ mixedExponentSemigroup ↔ ∃ ab : ℕ × ℕ, mixedExponent ab = t := Iff.rfl

/-- Every mixed exponent belongs to the semigroup. -/
theorem mixedExponent_mem (ab : ℕ × ℕ) : mixedExponent ab ∈ mixedExponentSemigroup :=
  ⟨ab, rfl⟩

/-- The semigroup lies in `[0, ∞)`. -/
theorem nonneg_of_mem_mixedExponentSemigroup {t : ℝ} (ht : t ∈ mixedExponentSemigroup) :
    0 ≤ t := by
  obtain ⟨ab, rfl⟩ := mem_mixedExponentSemigroup_iff.mp ht
  exact mixedExponent_nonneg ab

/-- **Mixed integrality, semigroup form.**  A two-base natural candidate takes natural values
at every exponent of `Λ_θ`. -/
theorem exists_nat_rpow_of_mem_mixedExponentSemigroup {m : ℕ}
    (hm : TwoBaseNaturalCandidate m) {t : ℝ} (ht : t ∈ mixedExponentSemigroup) :
    ∃ n : ℕ, (n : ℝ) = (m : ℝ) ^ t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := mem_mixedExponentSemigroup_iff.mp ht
  exact exists_nat_rpow_mixedExponent hm a b

/-! ### Order structure of the exponents -/

/-- Increasing the first coordinate strictly increases the mixed exponent. -/
theorem mixedExponent_lt_of_fst_lt {a a' b : ℕ} (h : a < a') :
    mixedExponent (a, b) < mixedExponent (a', b) := by
  simp only [mixedExponent_mk]
  have haa : (a : ℝ) < (a' : ℝ) := by exact_mod_cast h
  linarith

/-- Increasing the second coordinate strictly increases the mixed exponent, because
`θ > 0`. -/
theorem mixedExponent_lt_of_snd_lt {a b b' : ℕ} (h : b < b') :
    mixedExponent (a, b) < mixedExponent (a, b') := by
  simp only [mixedExponent_mk]
  have hbb : (b : ℝ) < (b' : ℝ) := by exact_mod_cast h
  have hmul := mul_lt_mul_of_pos_right hbb logThreeDivLogTwo_pos
  linarith

/-- `mixedExponent` is strictly monotone in its first coordinate. -/
theorem strictMono_mixedExponent_fst (b : ℕ) :
    StrictMono fun a : ℕ => mixedExponent (a, b) :=
  fun _ _ h => mixedExponent_lt_of_fst_lt h

/-- `mixedExponent` is strictly monotone in its second coordinate. -/
theorem strictMono_mixedExponent_snd (a : ℕ) :
    StrictMono fun b : ℕ => mixedExponent (a, b) :=
  fun _ _ h => mixedExponent_lt_of_snd_lt h

/-- Mixed exponents are monotone for the coordinatewise order on pairs. -/
theorem mixedExponent_le_mixedExponent {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    mixedExponent (a, b) ≤ mixedExponent (a', b') := by
  simp only [mixedExponent_mk]
  have haa : (a : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha
  have hbb : (b : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hb
  have hmul := mul_le_mul_of_nonneg_right hbb logThreeDivLogTwo_pos.le
  linarith

/-- A strict version of coordinatewise monotonicity: a strictly larger pair, in the
coordinatewise order, has a strictly larger mixed exponent.  Strictness uses injectivity,
hence the irrationality of `θ`. -/
theorem mixedExponent_lt_mixedExponent {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    (hne : (a, b) ≠ (a', b')) :
    mixedExponent (a, b) < mixedExponent (a', b') :=
  lt_of_le_of_ne (mixedExponent_le_mixedExponent ha hb) (mixedExponent_ne_of_ne hne)

/-! ### Elementary size bounds from `1 < θ < 2` -/

/-- Lower bound from `θ > 1`: the mixed exponent dominates `a + b`. -/
theorem add_le_mixedExponent (a b : ℕ) : (a : ℝ) + (b : ℝ) ≤ mixedExponent (a, b) := by
  simp only [mixedExponent_mk]
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hθ : (1 : ℝ) < logThreeDivLogTwo := one_lt_logThreeDivLogTwo
  have hmul : (0 : ℝ) ≤ (b : ℝ) * (logThreeDivLogTwo - 1) :=
    mul_nonneg hb (by linarith)
  nlinarith

/-- Upper bound from `θ < 8/5 < 2`: the mixed exponent is at most `a + 2 * b`. -/
theorem mixedExponent_le_add_two_mul (a b : ℕ) :
    mixedExponent (a, b) ≤ (a : ℝ) + 2 * (b : ℝ) := by
  simp only [mixedExponent_mk]
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hθ : logThreeDivLogTwo < (8 / 5 : ℝ) := logThreeDivLogTwo_lt_eight_fifths
  have hmul : (0 : ℝ) ≤ (b : ℝ) * (2 - logThreeDivLogTwo) :=
    mul_nonneg hb (by linarith)
  nlinarith

/-- **Square-box bound.**  Every exponent pair from the box `[0, q]²` has mixed exponent at
most `3 * q`.  Together with `card_image_mixedExponent` this is the counting input to the
report's crude semigroup lemma: the box supplies `(q + 1) ^ 2` distinct exponents, all below
`3 * q`. -/
theorem mixedExponent_le_three_mul {a b q : ℕ} (ha : a ≤ q) (hb : b ≤ q) :
    mixedExponent (a, b) ≤ 3 * (q : ℝ) := by
  have haq : (a : ℝ) ≤ (q : ℝ) := by exact_mod_cast ha
  have hbq : (b : ℝ) ≤ (q : ℝ) := by exact_mod_cast hb
  have h := mixedExponent_le_add_two_mul a b
  linarith

end

end LeanProofs.TwoBaseIntegerExponent
