import Mathlib.Data.Set.Card
import ExponentialIdentities.TwoBaseIntegerExponent.CandidateLattice

/-!
# The candidate valuation cone, divisor counting, and ambient root saturation

This file continues the lattice analysis begun in `CandidateLattice`.  There the two-base
natural candidates were shown to be closed under `gcd` and `lcm`; here the *shape* of the
candidate set inside `ℕ` is pinned down exactly, in the two operations that descent arguments
and searches actually use: divisibility, and extraction of roots.

Throughout, the conditional data of the exact primitive-generator theorem is packaged as the
predicate `CanonicalConeData w d a c`.  Under failure of `AlaogluErdosConjecture` such data
exists (`exists_canonicalConeData_of_not_alaogluErdosConjecture`), and every statement below is
phrased relative to it, so nothing here asserts anything about `ℕ` that would be false if the
conjecture holds.

The results are:

* **Coordinates and divisibility.**  For odd `w > 1` the coordinates `(s, t) ↦ 2 ^ s * w ^ t`
  are injective (`two_pow_mul_odd_pow_inj`) and divisibility is the coordinatewise order
  (`two_pow_mul_odd_pow_dvd_iff`).  These are unconditional statements about `ℕ`.
* **The valuation cone.**  `CanonicalConeData.twoBaseNaturalCandidate_coords_iff`:
  `2 ^ s * w ^ t` is a candidate exactly when `d ∣ t` and `a * t ≤ d * s`; and
  `CanonicalConeData.twoBaseNaturalCandidate_iff` turns that into a description of the whole
  candidate set.  This is the cone `Cand = {2 ^ s w ^ t : d ∣ t, d s ≥ a t}` of the report.
* **Divisor counting.**  `candidateDivisorFinset` is an explicit coordinate model of the
  candidate divisors of `2 ^ (n + a * k) * w ^ (d * k)`; its cardinality is computed exactly
  (`card_candidateDivisorFinset`), it is proved to be *exactly* the set of candidate divisors
  (`CanonicalConeData.coe_candidateDivisorFinset`), and the two combine into
  `CanonicalConeData.ncard_candidate_divisors`, the count `(k+1)(n+1) + a k (k+1) / 2`.
* **Candidates are not divisor-closed.**  Unless `d = 1`, `a = 0` and the odd core `w` is
  prime, some divisor of a candidate fails to be a candidate
  (`CanonicalConeData.exists_divisor_not_twoBaseNaturalCandidate`), equivalently
  `CanonicalConeData.prime_core_of_divisorClosed`.
* **Root saturation.**  `exists_coords_of_pow_eq_two_pow_mul_pow` shows that an integer with a
  positive power of the shape `2 ^ S * w ^ T` is itself of the shape `2 ^ s * w ^ t`, using the
  power-primitivity of the canonical odd core.  Combined with the cone description this yields
  the exact ambient saturation `CanonicalConeData.exists_pow_twoBaseNaturalCandidate_iff`, the
  least root exponent `CanonicalConeData.isLeast_root_exponent` (`d / gcd d t`), the index
  characterization `CanonicalConeData.isLeast_ambient_index` (the invariant `d`), and the
  criterion `CanonicalConeData.twoBaseNaturalCandidate_root_iff` telling exactly which integer
  roots of a candidate are again candidates.

Nothing in this file is a step toward a contradiction; the closure properties are compatible
with failure by construction.  No transcendence input and no analytic estimate is used: the
ingredients are unique factorization in `ℕ`, the power-primitivity of the canonical odd core,
and elementary lattice arithmetic on `ℕ²`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### Two-adic and odd-core coordinates -/

/-- **Uniqueness of the two-adic split.**  A power of two times an odd number determines both
factors.  This is the only place where unique factorization enters the coordinate calculus. -/
theorem two_pow_mul_odd_eq {A B X Y : ℕ} (hX : Odd X) (hY : Odd Y)
    (h : 2 ^ A * X = 2 ^ B * Y) : A = B ∧ X = Y := by
  have hX0 : X ≠ 0 := by
    have := Nat.odd_iff.mp hX
    omega
  have hY0 : Y ≠ 0 := by
    have := Nat.odd_iff.mp hY
    omega
  have hXfac : X.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hX.not_two_dvd_nat
  have hYfac : Y.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hY.not_two_dvd_nat
  have hfac := congrArg (fun m : ℕ ↦ m.factorization 2) h
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hX0,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hY0,
    Nat.factorization_pow, Nat.factorization_pow] at hfac
  have hAB : A = B := by
    simpa [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      (by norm_num : Nat.Prime 2).factorization_self, hXfac, hYfac] using hfac
  refine ⟨hAB, ?_⟩
  subst hAB
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < (2 : ℕ)) A) h

/-- **Injectivity of odd-core coordinates.**  For odd `w > 1` the pair of exponents in
`2 ^ s * w ^ t` is determined by the number itself. -/
theorem two_pow_mul_odd_pow_inj {w : ℕ} (hwodd : Odd w) (hw1 : 1 < w) {s₁ t₁ s₂ t₂ : ℕ}
    (h : 2 ^ s₁ * w ^ t₁ = 2 ^ s₂ * w ^ t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  obtain ⟨hs, hpow⟩ :=
    two_pow_mul_odd_eq (X := w ^ t₁) (Y := w ^ t₂) hwodd.pow hwodd.pow h
  exact ⟨hs, Nat.pow_right_injective (by omega) hpow⟩

/-- **Divisibility is the coordinatewise order.**  This is the divisibility criterion
`lt:eq-divisibility-coordinates` of the report, proved from the coordinatewise gcd formula of
`CandidateLattice`. -/
theorem two_pow_mul_odd_pow_dvd_iff {w : ℕ} (hwodd : Odd w) (hw1 : 1 < w)
    (s₁ t₁ s₂ t₂ : ℕ) :
    2 ^ s₁ * w ^ t₁ ∣ 2 ^ s₂ * w ^ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ := by
  constructor
  · intro hdvd
    have hg : Nat.gcd (2 ^ s₁ * w ^ t₁) (2 ^ s₂ * w ^ t₂) = 2 ^ s₁ * w ^ t₁ :=
      Nat.gcd_eq_left hdvd
    rw [gcd_two_pow_mul_odd_pow hwodd] at hg
    obtain ⟨hs, ht⟩ := two_pow_mul_odd_pow_inj hwodd hw1 hg
    omega
  · rintro ⟨hs, ht⟩
    exact Nat.mul_dvd_mul (pow_dvd_pow 2 hs) (pow_dvd_pow w ht)

/-- The primitive generator `2 ^ a * w ^ d` in odd-core coordinates. -/
theorem generator_pow_eq (w d a n k : ℕ) :
    (2 : ℕ) ^ n * (2 ^ a * w ^ d) ^ k = 2 ^ (n + a * k) * w ^ (d * k) := by
  rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
  ring

/-! ### The conditional data package -/

/-- **The canonical conditional data.**  This bundles exactly the part of the exact
primitive-generator theorem that the lattice analysis uses: an odd, power-primitive core `w`,
the rational-power index `d`, the base-adic depth `a` of the least generator, the base-three
output `c`, and the resulting characterization of the candidates in primitive coordinates.

Under failure of the conjecture such data exists; see
`exists_canonicalConeData_of_not_alaogluErdosConjecture`. -/
structure CanonicalConeData (w d a c : ℕ) : Prop where
  /-- The common odd core is odd. -/
  odd_core : Odd w
  /-- The common odd core is nontrivial. -/
  one_lt_core : 1 < w
  /-- The common odd core is power-primitive, in gcd-of-valuations form. -/
  primitive_core : oddPrimeValuationGCD w = 1
  /-- The rational-power index is positive. -/
  index_pos : 0 < d
  /-- The base-three output of the least generator is positive. -/
  output_pos : 0 < c
  /-- Either the base-adic depth vanishes or the base-three output is prime to three. -/
  three_free : a = 0 ∨ ¬ 3 ∣ c
  /-- Normalization of the `d`-th power of the odd-core exponential. -/
  normalized : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a
  /-- Every candidate has unique coordinates over the generator `2 ^ a * w ^ d`. -/
  candidate_coords : ∀ m : ℕ, TwoBaseNaturalCandidate m ↔
    ∃! nk : ℕ × ℕ, m = 2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2

/-- The odd core is positive. -/
theorem CanonicalConeData.core_pos {w d a c : ℕ} (hdata : CanonicalConeData w d a c) :
    0 < w := by
  have := hdata.one_lt_core
  omega

/-- The odd core is power-primitive in the `NatPowerPrimitive` sense. -/
theorem CanonicalConeData.natPowerPrimitive_core {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) : NatPowerPrimitive w :=
  natPowerPrimitive_of_oddPrimeValuationGCD_eq_one hdata.primitive_core

/-- **Existence of the canonical cone data.**  If the conjecture fails, the exact
primitive-generator theorem supplies the data package used throughout this file. -/
theorem exists_canonicalConeData_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ, CanonicalConeData w d a c := by
  obtain ⟨w, d, a, c, _β, hwodd, hw1, hprim, hd, hc, ha, _h7, _h8, hnorm, _h10, _h11,
    _h12, _h13, _h14, _h15, hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  exact ⟨w, d, a, c, ⟨hwodd, hw1, hprim, hd, hc, ha, hnorm, hcand⟩⟩

/-! ### The two-dimensional valuation cone -/

/-- **The candidate cone in odd-core coordinates.**  A number `2 ^ s * w ^ t` is a candidate
exactly when the odd-core exponent is divisible by the rational-power index and the pair
`(s, t)` lies in the rational cone `d s ≥ a t`.  This is Lemma `lt:lem-cone` of the report, in
the `w`-exponent parameterization `lt:eq-candidate-cone`. -/
theorem CanonicalConeData.twoBaseNaturalCandidate_coords_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (s t : ℕ) :
    TwoBaseNaturalCandidate (2 ^ s * w ^ t) ↔ d ∣ t ∧ a * t ≤ d * s := by
  constructor
  · intro hm
    obtain ⟨⟨n, k⟩, hnk, _⟩ := (hdata.candidate_coords _).mp hm
    have hnk' : (2 : ℕ) ^ s * w ^ t = 2 ^ (n + a * k) * w ^ (d * k) := by
      rw [hnk, generator_pow_eq]
    obtain ⟨hs, ht⟩ := two_pow_mul_odd_pow_inj hdata.odd_core hdata.one_lt_core hnk'
    subst hs
    subst ht
    refine ⟨⟨k, rfl⟩, ?_⟩
    have hcomm : a * (d * k) = d * (a * k) := by ring
    rw [hcomm]
    exact Nat.mul_le_mul_left d (Nat.le_add_left (a * k) n)
  · rintro ⟨⟨k, rfl⟩, hle⟩
    have hak : a * k ≤ s := by
      have hmul : d * (a * k) ≤ d * s := by
        calc d * (a * k) = a * (d * k) := by ring
          _ ≤ d * s := hle
      exact Nat.le_of_mul_le_mul_left hmul hdata.index_pos
    exact (twoBaseNaturalCandidate_primitive_coordinates_iff (w := w) (d := d) (a := a)
      (c := c) (i := s) (k := k) hdata.core_pos hdata.output_pos hdata.three_free
      hdata.normalized).mpr hak

/-- **The candidate set is exactly the cone.**  Every candidate has odd-core coordinates
satisfying the two cone conditions, and conversely. -/
theorem CanonicalConeData.twoBaseNaturalCandidate_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (m : ℕ) :
    TwoBaseNaturalCandidate m ↔ ∃ s t : ℕ, m = 2 ^ s * w ^ t ∧ d ∣ t ∧ a * t ≤ d * s := by
  constructor
  · intro hm
    obtain ⟨⟨n, k⟩, hnk, _⟩ := (hdata.candidate_coords m).mp hm
    refine ⟨n + a * k, d * k, ?_, ⟨k, rfl⟩, ?_⟩
    · rw [hnk, generator_pow_eq]
    · have hcomm : a * (d * k) = d * (a * k) := by ring
      rw [hcomm]
      exact Nat.mul_le_mul_left d (Nat.le_add_left (a * k) n)
  · rintro ⟨s, t, rfl, hdvd, hle⟩
    exact (hdata.twoBaseNaturalCandidate_coords_iff s t).mpr ⟨hdvd, hle⟩

/-! ### Counting the candidate divisors of a candidate -/

/-- The explicit coordinate model of the candidate divisors of `2 ^ (n + a * k) * w ^ (d * k)`.
The outer index `j` runs over `0, …, k` and records the *co-depth* `k - j` of the odd part; the
inner index `i` runs over `0, …, n + a * j` and records the excess two-adic valuation above the
cone boundary `a * (k - j)`.  Written this way both cardinalities are literal ranges. -/
def candidateDivisorFinset (w d a n k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).biUnion fun j =>
    (Finset.range (n + a * j + 1)).image fun i =>
      2 ^ (a * (k - j) + i) * w ^ (d * (k - j))

/-- Membership in the coordinate model, unfolded. -/
theorem mem_candidateDivisorFinset {w d a n k z : ℕ} :
    z ∈ candidateDivisorFinset w d a n k ↔
      ∃ j i : ℕ, j ≤ k ∧ i ≤ n + a * j ∧
        z = 2 ^ (a * (k - j) + i) * w ^ (d * (k - j)) := by
  unfold candidateDivisorFinset
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, i, by omega, by omega, rfl⟩
  · rintro ⟨j, i, hj, hi, rfl⟩
    exact ⟨j, by omega, i, by omega, rfl⟩

/-- The arithmetic progression behind the divisor count, in division-free form. -/
private theorem sum_range_affine_mul_two (a n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (n + a * j + 1)) * 2
      = ((k + 1) * (n + 1)) * 2 + a * (k * (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring

/-- Halving a division-free identity. -/
private theorem eq_add_div_two_of_mul_two {C A B : ℕ} (h : C * 2 = A * 2 + B) :
    C = A + B / 2 := by
  omega

/-- **The exact size of the coordinate model, division-free.** -/
theorem card_candidateDivisorFinset_mul_two {w d : ℕ} (hwodd : Odd w) (hw1 : 1 < w)
    (hd : 0 < d) (a n k : ℕ) :
    (candidateDivisorFinset w d a n k).card * 2
      = ((k + 1) * (n + 1)) * 2 + a * (k * (k + 1)) := by
  have hinj : ∀ j : ℕ, Function.Injective
      (fun i : ℕ => 2 ^ (a * (k - j) + i) * w ^ (d * (k - j))) := by
    intro j i₁ i₂ hEq
    have hEq' : (2 : ℕ) ^ (a * (k - j) + i₁) * w ^ (d * (k - j))
        = 2 ^ (a * (k - j) + i₂) * w ^ (d * (k - j)) := hEq
    have hexp := (two_pow_mul_odd_pow_inj hwodd hw1 hEq').1
    omega
  have hdisj : ((Finset.range (k + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j : ℕ => (Finset.range (n + a * j + 1)).image
        (fun i : ℕ => 2 ^ (a * (k - j) + i) * w ^ (d * (k - j)))) := by
    intro j₁ hj₁ j₂ hj₂ hne
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
    apply Finset.disjoint_left.mpr
    intro z hz₁ hz₂
    rw [Finset.mem_image] at hz₁ hz₂
    obtain ⟨i₁, _, rfl⟩ := hz₁
    obtain ⟨i₂, _, heq⟩ := hz₂
    have heq' : (2 : ℕ) ^ (a * (k - j₂) + i₂) * w ^ (d * (k - j₂))
        = 2 ^ (a * (k - j₁) + i₁) * w ^ (d * (k - j₁)) := heq
    have hcore := (two_pow_mul_odd_pow_inj hwodd hw1 heq').2
    have hsub := Nat.eq_of_mul_eq_mul_left hd hcore
    omega
  unfold candidateDivisorFinset
  rw [Finset.card_biUnion hdisj]
  have hcards : ∀ j ∈ Finset.range (k + 1),
      ((Finset.range (n + a * j + 1)).image
        (fun i : ℕ => 2 ^ (a * (k - j) + i) * w ^ (d * (k - j)))).card = n + a * j + 1 := by
    intro j _
    rw [Finset.card_image_of_injective _ (hinj j), Finset.card_range]
  rw [Finset.sum_congr rfl hcards]
  exact sum_range_affine_mul_two a n k

/-- **The exact size of the coordinate model.**  This is the count
`(k+1)(n+1) + a k (k+1) / 2` of Corollary `lt:cor-divisors`; the halving is exact because
`k (k + 1)` is even. -/
theorem card_candidateDivisorFinset {w d : ℕ} (hwodd : Odd w) (hw1 : 1 < w)
    (hd : 0 < d) (a n k : ℕ) :
    (candidateDivisorFinset w d a n k).card
      = (k + 1) * (n + 1) + a * k * (k + 1) / 2 := by
  have hmain := card_candidateDivisorFinset_mul_two hwodd hw1 hd a n k
  have hassoc : a * (k * (k + 1)) = a * k * (k + 1) := by ring
  rw [hassoc] at hmain
  exact eq_add_div_two_of_mul_two hmain

/-- **The coordinate model is exactly the set of candidate divisors.** -/
theorem CanonicalConeData.coe_candidateDivisorFinset {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (n k : ℕ) :
    (candidateDivisorFinset w d a n k : Set ℕ)
      = {u : ℕ | u ∣ 2 ^ (n + a * k) * w ^ (d * k) ∧ TwoBaseNaturalCandidate u} := by
  have hwodd := hdata.odd_core
  have hw1 := hdata.one_lt_core
  ext z
  rw [Finset.mem_coe, mem_candidateDivisorFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, i, hj, hi, rfl⟩
    have hsplit : a * (k - j) + a * j = a * k := by
      rw [← mul_add]
      congr 1
      omega
    refine ⟨?_, ?_⟩
    · rw [two_pow_mul_odd_pow_dvd_iff hwodd hw1]
      exact ⟨by omega, Nat.mul_le_mul_left d (Nat.sub_le k j)⟩
    · refine (hdata.twoBaseNaturalCandidate_coords_iff _ _).mpr ⟨dvd_mul_right d (k - j), ?_⟩
      have hcomm : a * (d * (k - j)) = d * (a * (k - j)) := by ring
      rw [hcomm]
      exact Nat.mul_le_mul_left d (Nat.le_add_right (a * (k - j)) i)
  · rintro ⟨hdvd, hcand⟩
    obtain ⟨s, t, rfl, ⟨p, rfl⟩, hle⟩ := (hdata.twoBaseNaturalCandidate_iff z).mp hcand
    rw [two_pow_mul_odd_pow_dvd_iff hwodd hw1] at hdvd
    obtain ⟨hs, ht⟩ := hdvd
    have hpk : p ≤ k := Nat.le_of_mul_le_mul_left ht hdata.index_pos
    have hap : a * p ≤ s := by
      have hmul : d * (a * p) ≤ d * s := by
        calc d * (a * p) = a * (d * p) := by ring
          _ ≤ d * s := hle
      exact Nat.le_of_mul_le_mul_left hmul hdata.index_pos
    have hsplit : a * (k - p) + a * p = a * k := by
      rw [← mul_add]
      congr 1
      omega
    have hkj : k - (k - p) = p := by omega
    refine ⟨k - p, s - a * p, by omega, by omega, ?_⟩
    rw [hkj]
    have hres : a * p + (s - a * p) = s := by omega
    rw [hres]

/-- **Counting candidate divisors.**  Under the conditional data, the number of candidates
dividing `2 ^ (n + a * k) * w ^ (d * k)` — that is, dividing `2 ^ n * (2 ^ a * w ^ d) ^ k` —
including `1` and the number itself, is `(k + 1) (n + 1) + a k (k + 1) / 2`.  This is
Corollary `lt:cor-divisors` of the report. -/
theorem CanonicalConeData.ncard_candidate_divisors {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (n k : ℕ) :
    {u : ℕ | u ∣ 2 ^ (n + a * k) * w ^ (d * k) ∧ TwoBaseNaturalCandidate u}.ncard
      = (k + 1) * (n + 1) + a * k * (k + 1) / 2 := by
  rw [← hdata.coe_candidateDivisorFinset n k, Set.ncard_coe_finset]
  exact card_candidateDivisorFinset hdata.odd_core hdata.one_lt_core hdata.index_pos a n k

/-! ### Candidates are not divisor-closed -/

/-- The odd core itself is a candidate only in the degenerate case `d = 1` and `a = 0`. -/
theorem CanonicalConeData.not_twoBaseNaturalCandidate_core {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (h : ¬ (d = 1 ∧ a = 0)) :
    ¬ TwoBaseNaturalCandidate w := by
  intro hw
  have hw' : TwoBaseNaturalCandidate (2 ^ 0 * w ^ 1) := by simpa using hw
  obtain ⟨hdvd, hle⟩ := (hdata.twoBaseNaturalCandidate_coords_iff 0 1).mp hw'
  exact h ⟨Nat.dvd_one.mp hdvd, by omega⟩

/-- **Candidates are not divisor-closed.**  Unless the rational-power index is `1`, the
base-adic depth is `0`, and the odd core is prime, some divisor of a candidate is not itself a
candidate.  This is the remark `lt:rem-not-divisor-closed` of the report, in the sharp form
that isolates the single degenerate configuration in which no obstruction arises. -/
theorem CanonicalConeData.exists_divisor_not_twoBaseNaturalCandidate {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (h : ¬ (d = 1 ∧ a = 0 ∧ Nat.Prime w)) :
    ∃ m u : ℕ, TwoBaseNaturalCandidate m ∧ u ∣ m ∧ 1 < u ∧ ¬ TwoBaseNaturalCandidate u := by
  have hgen : TwoBaseNaturalCandidate (2 ^ a * w ^ d) :=
    (hdata.twoBaseNaturalCandidate_coords_iff a d).mpr ⟨dvd_rfl, le_of_eq (Nat.mul_comm a d)⟩
  by_cases hda : d = 1 ∧ a = 0
  · have hnp : ¬ Nat.Prime w := fun hp => h ⟨hda.1, hda.2, hp⟩
    have hp : Nat.Prime w.minFac := Nat.minFac_prime (by have := hdata.one_lt_core; omega)
    have hne : w.minFac ≠ w := fun heq => hnp (heq ▸ hp)
    have hodd : Odd w.minFac := hdata.odd_core.of_dvd_nat (Nat.minFac_dvd w)
    refine ⟨2 ^ a * w ^ d, w.minFac, hgen, ?_, hp.one_lt, ?_⟩
    · exact dvd_mul_of_dvd_right
        ((Nat.minFac_dvd w).trans (dvd_pow_self w hdata.index_pos.ne')) (2 ^ a)
    · intro hcandp
      obtain ⟨s, t, hrep, _, _⟩ := (hdata.twoBaseNaturalCandidate_iff _).mp hcandp
      have hs0 : s = 0 := by
        by_contra hs
        have h2 : (2 : ℕ) ∣ w.minFac := by
          rw [hrep]
          exact dvd_mul_of_dvd_left (dvd_pow_self 2 hs) _
        have hoddval := Nat.odd_iff.mp hodd
        omega
      subst hs0
      rw [pow_zero, one_mul] at hrep
      rcases Nat.eq_zero_or_pos t with ht | ht
      · rw [ht, pow_zero] at hrep
        exact hp.one_lt.ne' hrep
      · have hwdvd : w ∣ w.minFac := by
          rw [hrep]
          exact dvd_pow_self w ht.ne'
        rcases hp.eq_one_or_self_of_dvd w hwdvd with h1 | h1
        · have := hdata.one_lt_core
          omega
        · exact hne h1.symm
  · refine ⟨2 ^ a * w ^ d, w, hgen, ?_, hdata.one_lt_core, ?_⟩
    · exact dvd_mul_of_dvd_right (dvd_pow_self w hdata.index_pos.ne') (2 ^ a)
    · exact hdata.not_twoBaseNaturalCandidate_core hda

/-- **Divisor closure forces the degenerate configuration.**  Contrapositive of
`CanonicalConeData.exists_divisor_not_twoBaseNaturalCandidate`. -/
theorem CanonicalConeData.prime_core_of_divisorClosed {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c)
    (hclosed : ∀ m u : ℕ, TwoBaseNaturalCandidate m → u ∣ m → 1 < u →
      TwoBaseNaturalCandidate u) :
    d = 1 ∧ a = 0 ∧ Nat.Prime w := by
  by_contra h
  obtain ⟨m, u, hm, hdvd, hu, hnot⟩ := hdata.exists_divisor_not_twoBaseNaturalCandidate h
  exact hnot (hclosed m u hm hdvd hu)

/-! ### Ambient root saturation -/

/-- A cancellation form of divisibility by a gcd quotient. -/
private theorem dvd_mul_of_coprime_factors {G D T r : ℕ} (hG : 0 < G)
    (hcop : Nat.Coprime D T) : G * D ∣ r * (G * T) ↔ D ∣ r := by
  constructor
  · intro hdvd
    have hcomm : r * (G * T) = G * (r * T) := by ring
    rw [hcomm] at hdvd
    exact hcop.dvd_of_dvd_mul_right ((Nat.mul_dvd_mul_iff_left hG).mp hdvd)
  · rintro ⟨q, rfl⟩
    exact ⟨q * T, by ring⟩

/-- Divisibility of a multiple in gcd-reduced form: `d ∣ r * t` exactly when the reduced index
`d / gcd d t` divides `r`. -/
theorem dvd_mul_iff_div_gcd_dvd {d t r : ℕ} (hd : 0 < d) :
    d ∣ r * t ↔ d / Nat.gcd d t ∣ r := by
  have hg : 0 < Nat.gcd d t := Nat.gcd_pos_of_pos_left t hd
  have hcop : Nat.Coprime (d / Nat.gcd d t) (t / Nat.gcd d t) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hd' : Nat.gcd d t * (d / Nat.gcd d t) = d :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left d t)
  have ht' : Nat.gcd d t * (t / Nat.gcd d t) = t :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right d t)
  calc d ∣ r * t
      ↔ Nat.gcd d t * (d / Nat.gcd d t) ∣ r * (Nat.gcd d t * (t / Nat.gcd d t)) := by
        rw [hd', ht']
    _ ↔ d / Nat.gcd d t ∣ r := dvd_mul_of_coprime_factors hg hcop

/-- **Ambient representability.**  If some positive power of `u` has the shape `2 ^ S * w ^ T`
for a power-primitive odd core `w > 1`, then `u` itself has the shape `2 ^ s * w ^ t`, and the
exponents scale by exactly `r`.  This replaces the Bézout step of the report's root-saturation
theorem: it is obtained from `Nat.exists_eq_pow_of_pow_eq_pow` together with the
power-primitivity of the canonical odd core. -/
theorem exists_coords_of_pow_eq_two_pow_mul_pow {w u r S T : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) (hprim : NatPowerPrimitive w)
    (hr : 0 < r) (hu : 0 < u) (h : u ^ r = 2 ^ S * w ^ T) :
    ∃ s t : ℕ, u = 2 ^ s * w ^ t ∧ S = r * s ∧ T = r * t := by
  obtain ⟨s, U, hUodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hu.ne'
  have hpow : ((2 : ℕ) ^ s * U) ^ r = 2 ^ (r * s) * U ^ r := by
    rw [mul_pow, ← pow_mul, mul_comm s r]
  rw [hpow] at h
  obtain ⟨hS, hUw⟩ :=
    two_pow_mul_odd_eq (X := U ^ r) (Y := w ^ T) hUodd.pow hwodd.pow h
  obtain ⟨cc, hUc, hwc⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hr.ne') hUw
  have hgpos : 0 < Nat.gcd r T := Nat.gcd_pos_of_pos_left T hr
  have hgdvd : Nat.gcd r T ∣ r := Nat.gcd_dvd_left r T
  have hrg : 0 < r / Nat.gcd r T := Nat.div_pos (Nat.le_of_dvd hr hgdvd) hgpos
  have hc1 : 1 < cc := by
    apply (one_lt_pow_iff hrg.ne').mp
    rw [← hwc]
    exact hw1
  have hrg1 : r / Nat.gcd r T = 1 := by
    by_contra hne
    exact hprim cc (r / Nat.gcd r T) hc1
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hrg.ne', hne⟩) hwc
  have hrgcd : r = Nat.gcd r T := by
    have hdc := Nat.div_mul_cancel hgdvd
    rw [hrg1, one_mul] at hdc
    exact hdc.symm
  have hrT : r ∣ T := by
    have hgT := Nat.gcd_dvd_right r T
    rwa [← hrgcd] at hgT
  obtain ⟨t, hT⟩ := hrT
  have hwc' : w = cc := by rw [hwc, hrg1, pow_one]
  have hexp : T / Nat.gcd r T = t := by
    rw [← hrgcd, hT]
    exact Nat.mul_div_cancel_left t hr
  have hUeq : U = w ^ t := by rw [hUc, hwc', hexp]
  exact ⟨s, t, by rw [hUeq], hS.symm, hT⟩

/-- **Powers in cone coordinates.**  For `r > 0` the power `(2 ^ s * w ^ t) ^ r` is a candidate
exactly when `d ∣ r * t` and the pair `(s, t)` already lies in the rational cone. -/
theorem CanonicalConeData.twoBaseNaturalCandidate_pow_coords_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (s t r : ℕ) (hr : 0 < r) :
    TwoBaseNaturalCandidate ((2 ^ s * w ^ t) ^ r) ↔ d ∣ r * t ∧ a * t ≤ d * s := by
  have hpow : ((2 : ℕ) ^ s * w ^ t) ^ r = 2 ^ (r * s) * w ^ (r * t) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm s r, mul_comm t r]
  rw [hpow, hdata.twoBaseNaturalCandidate_coords_iff]
  constructor
  · rintro ⟨hdvd, hle⟩
    refine ⟨hdvd, ?_⟩
    have hmul : r * (a * t) ≤ r * (d * s) := by
      calc r * (a * t) = a * (r * t) := by ring
        _ ≤ d * (r * s) := hle
        _ = r * (d * s) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hr
  · rintro ⟨hdvd, hle⟩
    refine ⟨hdvd, ?_⟩
    calc a * (r * t) = r * (a * t) := by ring
      _ ≤ r * (d * s) := Nat.mul_le_mul_left r hle
      _ = d * (r * s) := by ring

/-- **The least root exponent.**  For a cone point `2 ^ s * w ^ t` the least positive `r` with
`(2 ^ s * w ^ t) ^ r` a candidate is `d / gcd d t`.  This is the value `r_min` of the report's
root-saturation theorem. -/
theorem CanonicalConeData.isLeast_root_exponent {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) {s t : ℕ} (hcone : a * t ≤ d * s) :
    IsLeast {r : ℕ | 0 < r ∧ TwoBaseNaturalCandidate ((2 ^ s * w ^ t) ^ r)}
      (d / Nat.gcd d t) := by
  have hg : 0 < Nat.gcd d t := Nat.gcd_pos_of_pos_left t hdata.index_pos
  have hdg : 0 < d / Nat.gcd d t :=
    Nat.div_pos (Nat.le_of_dvd hdata.index_pos (Nat.gcd_dvd_left d t)) hg
  constructor
  · refine ⟨hdg, ?_⟩
    rw [hdata.twoBaseNaturalCandidate_pow_coords_iff s t _ hdg]
    exact ⟨(dvd_mul_iff_div_gcd_dvd hdata.index_pos).mpr dvd_rfl, hcone⟩
  · rintro r ⟨hr, hcand⟩
    rw [hdata.twoBaseNaturalCandidate_pow_coords_iff s t r hr] at hcand
    exact Nat.le_of_dvd hr ((dvd_mul_iff_div_gcd_dvd hdata.index_pos).mp hcand.1)

/-- **Root saturation in cone coordinates.**  A number of the shape `2 ^ s * w ^ t` has some
positive power inside the candidate set exactly when `(s, t)` lies in the rational cone
`d s ≥ a t`; the congruence `d ∣ t` is not needed. -/
theorem CanonicalConeData.exists_pow_twoBaseNaturalCandidate_coords_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) (s t : ℕ) :
    (∃ r : ℕ, 0 < r ∧ TwoBaseNaturalCandidate ((2 ^ s * w ^ t) ^ r)) ↔ a * t ≤ d * s := by
  constructor
  · rintro ⟨r, hr, hcand⟩
    exact ((hdata.twoBaseNaturalCandidate_pow_coords_iff s t r hr).mp hcand).2
  · intro hcone
    exact ⟨_, (hdata.isLeast_root_exponent hcone).1⟩

/-- **Exact ambient root saturation.**  The set of positive integers admitting some positive
power inside the candidate set is exactly the set of lattice points of the rational cone
`d s ≥ a t`.  This is the report's theorem `lt:thm-root-saturation`. -/
theorem CanonicalConeData.exists_pow_twoBaseNaturalCandidate_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) {u : ℕ} (hu : 0 < u) :
    (∃ r : ℕ, 0 < r ∧ TwoBaseNaturalCandidate (u ^ r)) ↔
      ∃ s t : ℕ, u = 2 ^ s * w ^ t ∧ a * t ≤ d * s := by
  constructor
  · rintro ⟨r, hr, hcand⟩
    obtain ⟨S, T, hrep, _, hle⟩ := (hdata.twoBaseNaturalCandidate_iff _).mp hcand
    obtain ⟨s, t, hueq, hS, hT⟩ :=
      exists_coords_of_pow_eq_two_pow_mul_pow hdata.odd_core hdata.one_lt_core
        hdata.natPowerPrimitive_core hr hu hrep
    refine ⟨s, t, hueq, ?_⟩
    subst hS
    subst hT
    have hmul : r * (a * t) ≤ r * (d * s) := by
      calc r * (a * t) = a * (r * t) := by ring
        _ ≤ d * (r * s) := hle
        _ = r * (d * s) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hr
  · rintro ⟨s, t, rfl, hcone⟩
    exact (hdata.exists_pow_twoBaseNaturalCandidate_coords_iff s t).mpr hcone

/-- **The ambient saturation index.**  The rational-power index `d` is the least positive `r`
such that some `(2 ^ s * w) ^ r` is a candidate.  This is Corollary `lt:cor-ambient-index`. -/
theorem CanonicalConeData.isLeast_ambient_index {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) :
    IsLeast {r : ℕ | 0 < r ∧ ∃ s : ℕ, TwoBaseNaturalCandidate ((2 ^ s * w) ^ r)} d := by
  have hrw : ∀ s : ℕ, (2 : ℕ) ^ s * w = 2 ^ s * w ^ 1 := by
    intro s
    rw [pow_one]
  constructor
  · refine ⟨hdata.index_pos, a, ?_⟩
    rw [hrw a, hdata.twoBaseNaturalCandidate_pow_coords_iff a 1 d hdata.index_pos]
    refine ⟨dvd_mul_right d 1, ?_⟩
    calc a * 1 = a := by ring
      _ ≤ d * a := Nat.le_mul_of_pos_left a hdata.index_pos
  · rintro r ⟨hr, s, hcand⟩
    rw [hrw s, hdata.twoBaseNaturalCandidate_pow_coords_iff s 1 r hr] at hcand
    have hdr : d ∣ r := by
      have hdr1 := hcand.1
      rwa [mul_one] at hdr1
    exact Nat.le_of_dvd hr hdr

/-- **Saturation is trivial exactly at index one.**  The candidate set exhausts the cone
`d s ≥ a t` if and only if `d = 1`; for `d > 1` the congruence `d ∣ t` is a genuine
finite-index defect. -/
theorem CanonicalConeData.index_eq_one_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) :
    (∀ s t : ℕ, a * t ≤ d * s → TwoBaseNaturalCandidate (2 ^ s * w ^ t)) ↔ d = 1 := by
  constructor
  · intro h
    have hbound : a * 1 ≤ d * a := by
      calc a * 1 = a := by ring
        _ ≤ d * a := Nat.le_mul_of_pos_left a hdata.index_pos
    have hcand := h a 1 hbound
    exact Nat.dvd_one.mp ((hdata.twoBaseNaturalCandidate_coords_iff a 1).mp hcand).1
  · intro hd1 s t hle
    refine (hdata.twoBaseNaturalCandidate_coords_iff s t).mpr ⟨?_, hle⟩
    rw [hd1]
    exact one_dvd t

/-! ### Which integer roots of a candidate are again candidates -/

/-- The explicit `e`-th root of a candidate whose primitive coordinates are both divisible by
`e`. -/
theorem CanonicalConeData.root_eq {w d a c : ℕ} (hdata : CanonicalConeData w d a c)
    {u e n k : ℕ} (he : 0 < e) (hu : u ^ e = 2 ^ n * (2 ^ a * w ^ d) ^ k)
    (hn : e ∣ n) (hk : e ∣ k) :
    u = 2 ^ (n / e) * (2 ^ a * w ^ d) ^ (k / e) := by
  have hv : ((2 : ℕ) ^ (n / e) * (2 ^ a * w ^ d) ^ (k / e)) ^ e
      = 2 ^ n * (2 ^ a * w ^ d) ^ k := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.div_mul_cancel hn, Nat.div_mul_cancel hk]
  exact (Nat.pow_left_inj he.ne').mp (hu.trans hv.symm)

/-- **Which integer roots survive as candidates.**  If `u ^ e` is the candidate with primitive
coordinates `(n, k)` and `e ≥ 1`, then `u` is itself a candidate exactly when `e` divides both
coordinates.  This is Corollary `lt:cor-roots`(b) of the report; every such root lies in the
ambient saturation, and this criterion says exactly when it descends into the candidate set
itself. -/
theorem CanonicalConeData.twoBaseNaturalCandidate_root_iff {w d a c : ℕ}
    (hdata : CanonicalConeData w d a c) {u e n k : ℕ} (he : 0 < e)
    (hu : u ^ e = 2 ^ n * (2 ^ a * w ^ d) ^ k) :
    TwoBaseNaturalCandidate u ↔ e ∣ n ∧ e ∣ k := by
  constructor
  · intro hcand
    obtain ⟨⟨n', k'⟩, hnk, _⟩ := (hdata.candidate_coords u).mp hcand
    have hu' : u = 2 ^ (n' + a * k') * w ^ (d * k') := by
      rw [hnk, generator_pow_eq]
    have hleft : u ^ e = 2 ^ ((n' + a * k') * e) * w ^ ((d * k') * e) := by
      rw [hu', mul_pow, ← pow_mul, ← pow_mul]
    rw [generator_pow_eq] at hu
    obtain ⟨h2, hcore⟩ :=
      two_pow_mul_odd_pow_inj hdata.odd_core hdata.one_lt_core (hleft.symm.trans hu)
    have hcore' : d * (k' * e) = d * k := by
      rw [← mul_assoc]
      exact hcore
    have hk : k' * e = k := Nat.eq_of_mul_eq_mul_left hdata.index_pos hcore'
    have hn : n' * e = n := by
      have hexpand : (n' + a * k') * e = n' * e + (a * k') * e := by ring
      have hak : a * k = (a * k') * e := by
        rw [← hk]
        ring
      rw [hexpand, hak] at h2
      omega
    exact ⟨⟨n', by rw [← hn]; ring⟩, ⟨k', by rw [← hk]; ring⟩⟩
  · rintro ⟨hn, hk⟩
    have hueq := hdata.root_eq he hu hn hk
    rw [hueq, generator_pow_eq]
    exact (twoBaseNaturalCandidate_primitive_coordinates_iff (w := w) (d := d) (a := a)
      (c := c) (i := n / e + a * (k / e)) (k := k / e) hdata.core_pos hdata.output_pos
      hdata.three_free hdata.normalized).mpr (Nat.le_add_left _ _)

end LeanProofs.TwoBaseIntegerExponent
