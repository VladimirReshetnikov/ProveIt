import New.UpperBound.Divisibility.JetExponent

/-!
# Marked primes above `p`, full marks and the scaled Hecke operator

Fix a prime `p` and an embedding `ι : ℂ → ℂ_[p]`. Each infinite place of `E` then induces a prime
above `p`. A finite set `Λ` of such primes is marked if it is disjoint from its conjugate and each
member is induced by an a-place; the definition also asks that `p` be exceptional and below `x₁`.
A *full mark* is a marked set that contains, for each a-place, the prime it induces or the
conjugate of that prime.
This file shows that a full mark exists and defines, with `A_𝔩` the number
`New.Data.heckeScalingExponent` of a prime `𝔩`, a scaled Hecke operator on the space
`D.SourceForm` of source forms.

## Main definitions and results

* `New.Data.IsFullMark`: a marked set that meets each pair of a prime induced by an a-place and its
  conjugate.
* `New.Data.exists_isFullMark`: a full mark exists for every exceptional `p < x₁`.
* `New.Data.IsMarked.scaledHeckeOperator`: the operator `p ^ A_𝔩 • T_{𝔩,𝔯}` at a marked prime, on
  the space of source forms.

Notions from other files:
* `New.Data.aPlaces`: The `a`-places: the infinite places of `E` whose class in `(ℤ/q₁)ˣ` is `1`
  modulo `q₀`.
* `New.Data.IsExceptional`, `New.Data.ceilLogLifts`: A condition on `p` alone: `(p/d) = -1`,
  `p ≢ ±1` modulo `m`, and the order `o₀` of `-p` modulo `q₀` is odd and at most `𝔯`, the least
  natural number with `m ≤ p^𝔯`.
* `New.placeOfEmb`: The prime of `E` induced by an embedding `σ : E →+* F` into an ultrametric
  normed field over `ℚ_p`: the centre on the integers of `E` of the valuation ring
  `{x : E | ‖σ x‖ ≤ 1}`.
* `New.Data.placeOfInt`: The infinite place of E named by the class of the integer ν modulo q₁ if ν
  is prime to q₁, and the identity place otherwise.
* `New.Data.lowColumns`: the number of columns at `τ` of height below `n_{j+1}` and different
  from `1`.
-/

noncomputable section

namespace New.Data

/-! ## Induced primes and marked sets -/

section MarkedDefs

open Finset

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  (Λ : Finset (FinPlace D.E))

/-- The prime of `E` above `p` induced by the embedding `ι ∘ σ` of `E` into `ℂ_p`, where the
infinite place `σ` is read as the embedding of `E` into `ℂ` that the CM type selects. -/
def inducedPlace (σ : D.Φ) : FinPlace D.E := placeOfEmb (ιₚ.comp (Φ σ))

/-- A marked set of primes of `E` at `ι`: `Λ` is disjoint from its complex conjugate, and each prime
of `Λ` is induced by an a-place. Moreover `p` is exceptional and below `x₁`. -/
structure IsMarked where
  /-- `Λ` is disjoint from its complex conjugate. -/
  star_notMem : ∀ l ∈ Λ, star l ∉ Λ
  /-- `p` is exceptional. -/
  isExceptional : D.IsExceptional p
  /-- Each prime of `Λ` is induced by an a-place. -/
  induced_by_aPlace : ∀ l ∈ Λ, ∃ τ ∈ D.aPlaces, inducedPlace τ = l
  /-- `p` is below `x₁` and `χ_K(p) ≠ 1`. -/
  isSmallNonsplit : D.IsSmallNonsplit p

/-- A full mark: a marked set that contains, for each a-place `τ`, the prime induced by `τ` or its
conjugate. -/
structure IsFullMark extends D.IsMarked Λ where
  /-- For each a-place, `Λ` contains its induced prime or the conjugate of that prime. -/
  mem_or_star_mem : ∀ τ ∈ D.aPlaces, inducedPlace τ ∈ Λ ∨ star (inducedPlace τ) ∈ Λ

/-- The module of integral source forms: the elements of `D.SourceForm` of gauge at most `1`. -/
abbrev integralSourceForms : Submodule embValRing D.SourceForm :=
  (integralFormsAt D.SourceForm 1).comap (D.SourceForm.subtype.restrictScalars embValRing)

open scoped Classical in
/-- The places inducing a prime of `Λ`: the infinite places of `E` whose induced prime above `p`
lies in `Λ`. -/
abbrev placesInducing : Finset D.Φ := {σ : D.Φ | inducedPlace σ ∈ Λ}

open scoped Classical in
/-- The places inducing the conjugate of a prime of `Λ`: the infinite places of `E` whose induced
prime above `p` is conjugate to a prime of `Λ`. -/
abbrev placesInducingConj : Finset D.Φ := {σ : D.Φ | star (inducedPlace σ) ∈ Λ}

open scoped Classical in
/-- The number `A_𝔩`: the integer `D.a` times the number of a-places (places of class `1` modulo
`q₀`) that induce the prime `𝔩` at `ι`. -/
def heckeScalingExponent (l : FinPlace D.E) : ℕ := D.a * #{τ ∈ D.aPlaces | inducedPlace τ = l}

/-- The numbers `A_𝔩` for `𝔩 ∈ Λ` add up to `a` times the number of a-places whose induced prime
lies in `Λ`. -/
lemma sum_heckeScalingExponent : ∑ l ∈ Λ,
  heckeScalingExponent l = D.a * #(D.aPlaces ∩ placesInducing Λ) := by
  classical
  simp only [heckeScalingExponent, ← mul_sum, inter_filter, inter_univ]
  -- The `convert` only matches the decidability instances of the two filters.
  convert congrArg (D.a * ·) (sum_card_fiberwise_eq_card_filter D.aPlaces Λ inducedPlace) using 4

end MarkedDefs

/-! ## Existence and properties of marked sets above a non-split prime -/

section MarkedPrimes

open Finset Parameters Real Nat

variable {P : Parameters} {D : Data P} {p : ℕ} [hq : Fact p.Prime]

/-- An exceptional prime is inert in `K`: its Legendre symbol `(p/d)` is `-1`. -/
lemma IsExceptional.chiK_eq_neg_one {p : ℕ} (h : D.IsExceptional p) : chiK P.d p = -1 := h.1

/-- For an exceptional prime `p` the order `o₀` of `-p` modulo `q₀` is odd. -/
lemma IsExceptional.odd_o₀ {p : ℕ} (h : D.IsExceptional p) : Odd (D.o₀ p) := by
  grind [IsExceptional]

/-- `D.ceilLogLifts p`, the least natural number `k` with `m ≤ p ^ k`, is at most `D.towerExp`, the
exponent `s` with `2 ^ s = m ^ 22`. -/
lemma ceilLogLifts_le_towerExp : D.ceilLogLifts p ≤ D.towerExp := by
  obtain ⟨e, hm, hs⟩ := D.exists_m_eq_two_pow
  refine clog_le_of_le_pow (hm.trans_le ?_)
  exact (Nat.pow_le_pow_right two_pos (by lia)).trans (Nat.pow_le_pow_left hq.out.two_le D.towerExp)

/-- The least `r` with `m ≤ p ^ r` is at most `l₀`, the least power of `3` above `27 s`, because
`m ≤ 2 ^ l₀`. -/
lemma ceilLogLifts_le_l₀ : D.ceilLogLifts p ≤ l₀ D.towerExp := by
  refine clog_le_of_le_pow ?_
  calc D.m ≤ D.m ^ 594 := Nat.le_self_pow (by norm_num) _
    _ ≤ 2 ^ l₀ D.towerExp := D.m_pow_le_two_pow_l₀
    _ ≤ p ^ l₀ D.towerExp := Nat.pow_le_pow_left hq.out.two_le _

/-- The number `ceilLogLifts p`, the least `𝔯` with `m ≤ p ^ 𝔯`, is bounded in order of magnitude by
`log (log x₁)`: it is at most `s` (`ceilLogLifts_le_towerExp`). -/
instance : D.HasLogUpper (D.ceilLogLifts p) (Real.log D.logX₁) :=
  D.hasLogUpper_of_le (A := D.towerExp) ceilLogLifts_le_towerExp

/-- If `2 ^ s` divides a product of two natural numbers, where `2 * e < s`, and `2 ^ (e + 1)` does
not divide the first factor, then `2 ^ (e + 1)` divides the second. -/
lemma two_pow_dvd_right_of_dvd_mul {e s q o : ℕ} (hs : 2 * e < s) (h_dvd : 2 ^ s ∣ q * o)
    (hq : ¬2 ^ (e + 1) ∣ q) : 2 ^ (e + 1) ∣ o := by
  -- Compare `2`-adic valuations: that of `q` is at most `e`, that of `q * o` at least `s`.
  simp only [padicValNat_dvd_iff, mul_eq_zero, not_or, not_le] at h_dvd hq ⊢
  grind [padicValNat.mul]

/-- Let `p` be an exceptional prime: inert in `K = ℚ(√-d)`, not congruent to `±1` modulo the number
`m` of lifts, and such that the order `o₀` of `-p` modulo `q₀` is odd and at most `ceilLogLifts p`,
the least `r` with `m ≤ p ^ r`. Then the power of two `m` divides the order of `D.placeOfInt (-p)`,
the class of `-p` in the group `Gal(E/K) = (ℤ/q₁)ˣ` of infinite places of `E = K(ζ_{q₁})`. -/
lemma IsExceptional.m_dvd_orderOf (h : D.IsExceptional p) : D.m ∣ orderOf (D.placeOfInt (-p)) := by
  -- With `o` the order of `-p`, lifting the exponent gives `2 ^ s ∣ (-p ± 1) * o`. Here `m` is a
  -- power of `2`, `2 ^ s = m ^ 22` and `m` does not divide `p ± 1`, so `m` divides `o`.
  obtain ⟨e, (hm : D.m = 2 ^ (e + 1)), (hs : D.towerExp = (e + 1) * 22)⟩ := D.exists_m_eq_two_pow
  obtain ⟨(h_inert : chiK P.d p = -1), (h_not_pm_one : ¬D.IsPlusMinusOneModLifts p), -⟩ := h
  set o : ℕ := orderOf (D.placeOfInt (-p))
  have h_not_dvd : ¬p ∣ P.q₁ 0 := by grind [not_dvd_q₁_mul_d_of_inert h_inert (s := 0)]
  have h_pow : ((-p : ℤ) : ZMod (2 ^ (D.towerExp + 1))) ^ o = 1 := by
    rw [← placeClass_placeOfInt (h_dvd := two_pow_dvd_q₁)
        (isCoprime_q₀_of_not_dvd h_not_dvd).neg_left,
      ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  obtain ⟨h_sub, h_add⟩ : ¬2 ^ (e + 1) ∣ p - 1 ∧ ¬2 ^ (e + 1) ∣ p + 1 := by
    simpa [IsPlusMinusOneModLifts, hm] using h_not_pm_one
  have hp_one : 1 ≤ p := hq.out.one_le
  rw [hm]
  rcases two_pow_dvd_or_of_pow_eq_one (orderOf_pos _) h_pow with h_dvd | h_dvd <;>
    rw [hm, ← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at *
  · rw [show ((-p : ℤ) - 1).natAbs = p + 1 by lia] at h_dvd
    exact two_pow_dvd_right_of_dvd_mul (by lia) h_dvd h_add
  · rw [show ((-p : ℤ) + 1).natAbs = p - 1 by lia] at h_dvd
    exact two_pow_dvd_right_of_dvd_mul (by lia) h_dvd h_sub

/-- For an exceptional prime `p`, every prime `w` of `E` above `p` has norm `p ^ o`, where `o` is
the order of the place named by `-p`. -/
lemma IsExceptional.q_eq_pow_orderOf (h : D.IsExceptional p) {w : FinPlace D.E}
    (hw : ↑p ∈ w.asIdeal) :
    w.q = p ^ orderOf (D.placeOfInt (-p)) := by
  rw [q_eq_pow_lcm_of_inert hw h.chiK_eq_neg_one,
    Nat.lcm_eq_left (D.m_even.two_dvd.trans h.m_dvd_orderOf)]

/-- For an exceptional prime `p`, no prime `w` of `E` above `p` is equal to its complex
conjugate. -/
lemma IsExceptional.star_ne (h : D.IsExceptional p) {w : FinPlace D.E} (hw : ↑p ∈ w.asIdeal) :
    star w ≠ w := by
  -- The places that send `w` to its conjugate are the odd powers of `-p`. The order of `-p` is
  -- even, so the identity is not one of them.
  intro h_eq
  -- The action on primes is a bare `SMul`, so `one_smul` does not apply.
  have h_one : (1 : D.Φ) • w = w := (smul_eq_self_iff_of_inert hw h.chiK_eq_neg_one).2 ⟨0, by simp⟩
  obtain ⟨i, hi_eq, hi_odd⟩ : ∃ i : ℕ, 1 = D.placeOfInt (-p) ^ i ∧ Odd i :=
    (smul_eq_star_iff_of_inert hw h.chiK_eq_neg_one).1 (h_one.trans h_eq.symm)
  exact hi_odd.not_two_dvd_nat
    ((D.m_even.two_dvd.trans h.m_dvd_orderOf).trans (orderOf_dvd_of_pow_eq_one hi_eq.symm))

/-- A non-split prime `p < x₁` divides neither `D.M` (the product of the two level primes
`D.levelPrime i`) nor `D.M * D.N`, and differs from `N`: the prime factors of `D.M * D.N` are at
least `x₁`. -/
lemma IsSmallNonsplit.not_dvd_M_mul_N (h : D.IsSmallNonsplit p) :
    ¬p ∣ D.M ∧ p ≠ D.N ∧ ¬p ∣ D.M * D.N := by
  have hN : D.x₁ ≤ D.N := D.le_of_hasLogBound
  have hg (i : Fin 2) : D.x₁ ≤ D.levelPrime i := D.le_of_hasLogBound
  have h_ne : p ≠ D.levelPrime 0 ∧ p ≠ D.levelPrime 1 ∧ p ≠ D.N := by grind [h.1]
  grind [M, hq.out, levelPrime_prime, N_prime, Nat.Prime.dvd_mul, Nat.prime_dvd_prime_iff_eq]

variable (D) [PadicPlace p]

/-! ### Induced primes and the existence of a marked set -/

/-- The prime induced by an infinite place lies above `p`. -/
lemma p_mem_inducedPlace (σ : D.Φ) : ↑p ∈ (D.inducedPlace σ).asIdeal := natCast_mem_placeOfEmb _

/-- Multiplying `σ` by `τ` pulls the induced prime back along `τ` in `Gal(E/K)`, that is, moves it
by `τ⁻¹`. The action `•` of infinite places on primes is this pullback. -/
lemma inducedPlace_mul (σ τ : D.Φ) : D.inducedPlace (σ * τ) = τ • inducedPlace σ := by
  ext
  simp [inducedPlace, phi_mul]

/-- For p inert in K and e odd, the prime induced by (−p^e)σ is the conjugate of the prime
induced by σ. -/
lemma inducedPlace_neg_pow_mul_of_odd (h_inert : chiK P.d p = -1) {e : ℕ} (he : Odd e) (σ : D.Φ) :
    D.inducedPlace (D.placeOfInt (-p ^ e) * σ) = star (inducedPlace σ) := by
  rw [mul_comm, inducedPlace_mul]
  exact (smul_eq_star_iff_of_inert (D.p_mem_inducedPlace σ) h_inert).2
    ⟨e, by rw [placeOfInt_pow, he.neg_pow], he⟩

/-- Let `p` be a prime below the cut-off `x₁` that is exceptional: `(p/d) = -1`, `p ≢ ±1` modulo
`m`, and the order of `-p` modulo `q₀` is odd and at most `ceilLogLifts p`, the least `r` with
`m ≤ p ^ r`. Then there is a full mark: a finite set of primes of `E` induced by a-places and
disjoint from its conjugate, which contains `𝔩` or its conjugate for each prime `𝔩` induced by an
a-place. -/
lemma exists_isFullMark (hp_lt : p < D.x₁) (h_exceptional : D.IsExceptional p) :
    ∃ Λ : Finset (FinPlace D.E), D.IsFullMark Λ := by
  -- Take the primes induced by a-places that are smaller than their conjugates, for some linear
  -- order on the primes.
  obtain ⟨(_ : LinearOrder (FinPlace D.E)), -⟩ := exists_wellFoundedLT (FinPlace D.E)
  refine ⟨{l ∈ D.aPlaces.image inducedPlace | l < star l}, ?_, fun τ hτ ↦ ?_⟩
  · exact
      { star_notMem := by grind [star_star]
        isExceptional := h_exceptional
        induced_by_aPlace := by grind
        isSmallNonsplit := ⟨hp_lt, by simp [h_exceptional.chiK_eq_neg_one]⟩ }
  -- As `o₀` is odd, `-p ^ o₀ * τ` is an a-place that induces the conjugate prime.
  have h_aPlace : D.placeOfInt (-p ^ D.o₀ p) * τ ∈ D.aPlaces :=
    (D.placeOfInt_mul_mem_aPlaces_iff h_exceptional.odd_o₀ τ hτ).2 dvd_rfl
  have h_conj : inducedPlace (D.placeOfInt (-p ^ D.o₀ p) * τ) = star (inducedPlace τ) :=
    D.inducedPlace_neg_pow_mul_of_odd h_exceptional.chiK_eq_neg_one h_exceptional.odd_o₀ τ
  have h_star : star (inducedPlace τ) ≠ inducedPlace τ :=
    h_exceptional.star_ne (D.p_mem_inducedPlace τ)
  grind [star_star]

variable {D} {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E}

/-- Let `p` be a prime with `(p/d) = -1`. Two places induce the same prime or conjugate primes
exactly when they differ by a power of `D.placeOfInt (-p)`, the place of the class of `-p` modulo
`q₁`. -/
lemma inducedPlace_eq_or_star_iff (h_inert : chiK P.d p = -1) (σ τ : D.Φ) :
    D.inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ) ↔
      ∃ i : ℕ, σ = D.placeOfInt (-p) ^ i * τ := by
  -- Even powers of `-p` fix a prime above `p` (`smul_eq_self_iff_of_inert`), odd powers conjugate
  -- it.
  have h_div : inducedPlace σ = (σ / τ) • inducedPlace τ := by
    rw [← inducedPlace_mul, mul_div_cancel]
  rw [h_div, smul_eq_self_iff_of_inert (D.p_mem_inducedPlace τ) h_inert,
    smul_eq_star_iff_of_inert (D.p_mem_inducedPlace τ) h_inert]
  grind [Nat.even_or_odd, div_eq_iff_eq_mul]

/-- The properties of the orbits of the place named by `-p` that hold at an exceptional prime `p`.
Write `o₀ = D.o₀ p` for the order of `-p` modulo `q₀`, `o` for the order of the place named by `-p`,
`r = D.ceilLogLifts p` for the least number with `m ≤ p ^ r`, `l₀` for the least power of `3` above
`27 s`, where `2 ^ s = m ^ 22`, and `w_τ` for the prime above `p` induced by the infinite place
`τ`. -/
structure HasExceptionalOrbits (D : Data P) (p : ℕ) [Fact p.Prime] [PadicPlace p] : Prop where
  /-- `o₀` is odd. -/
  odd_o₀ : Odd (D.o₀ p)
  /-- `o₀ ≤ r`. -/
  o₀_le_ceilLogLifts : D.o₀ p ≤ D.ceilLogLifts p
  /-- `r ≤ l₀`. -/
  ceilLogLifts_le_l₀ : D.ceilLogLifts p ≤ l₀ D.towerExp
  /-- `m` divides `o`. -/
  m_dvd_orderOf : D.m ∣ orderOf (D.placeOfInt (-p))
  /-- Each `w_τ` has norm `p ^ o`. -/
  q_inducedPlace : ∀ τ : D.Φ, (D.inducedPlace τ).q = p ^ orderOf (D.placeOfInt (-p))
  /-- For odd `e`, the place `(-p ^ e) τ` induces the conjugate of `w_τ`. -/
  inducedPlace_neg_pow_mul : ∀ τ : D.Φ, ∀ e : ℕ, Odd e →
    D.inducedPlace (D.placeOfInt (-p ^ e) * τ) = star (D.inducedPlace τ)
  /-- The conjugate of `w_τ` differs from `w_τ`. -/
  star_ne : ∀ τ : D.Φ, star (D.inducedPlace τ) ≠ D.inducedPlace τ
  /-- The places that induce `w_τ` or its conjugate are the `(-p) ^ i τ`. -/
  eq_or_star_iff : ∀ σ τ : D.Φ,
    D.inducedPlace σ = D.inducedPlace τ ∨ D.inducedPlace σ = star (D.inducedPlace τ) ↔
      ∃ i : ℕ, σ = D.placeOfInt (-p) ^ i * τ

/-- Let `p` be an exceptional prime: `(p/d) = -1`, `p ≢ ±1` modulo `m`, and the order `o₀` of `-p`
modulo `q₀` is odd and at most `r = ceilLogLifts p`, the least number with `m ≤ p ^ r`. Then the
properties of `New.Data.HasExceptionalOrbits` hold: `o₀ ≤ r ≤ l₀`, the least power of `3` above
`27 s` with `2 ^ s = m ^ 22`. The order `o` of the place named by `-p` is a multiple of `m`. The
prime `w_τ = inducedPlace τ` of `E` above `p` induced by an infinite place `τ` has absolute norm
`p ^ o` and differs from its conjugate, which is induced by `(-p ^ e) τ` for odd `e`. The places
that induce `w_τ` or its conjugate are the `(-p) ^ i τ`. -/
theorem IsExceptional.hasExceptionalOrbits (h : D.IsExceptional p) :
    D.HasExceptionalOrbits p where
  odd_o₀ := h.odd_o₀
  o₀_le_ceilLogLifts := by grind [IsExceptional]
  ceilLogLifts_le_l₀ := ceilLogLifts_le_l₀
  m_dvd_orderOf := h.m_dvd_orderOf
  q_inducedPlace τ := h.q_eq_pow_orderOf (D.p_mem_inducedPlace τ)
  inducedPlace_neg_pow_mul τ _ he := D.inducedPlace_neg_pow_mul_of_odd h.chiK_eq_neg_one he τ
  star_ne τ := h.star_ne (D.p_mem_inducedPlace τ)
  eq_or_star_iff := inducedPlace_eq_or_star_iff h.chiK_eq_neg_one

/-! ### Properties of marked sets -/

/-- A marked set has at most `f` primes, `f` being the number of infinite places of `E`: each of its
primes is induced by one of them. -/
lemma IsMarked.card_le (h : D.IsMarked Λ) : #Λ ≤ D.f :=
  card_le_card_of_surjOn inducedPlace fun l hl ↦
    (h.induced_by_aPlace l hl).imp fun τ hτ ↦ ⟨mem_univ τ, hτ.2⟩

/-- For a marked set `Λ`, the prime `p` divides neither `D.M` nor `D.M * D.N`, and differs
from `N`. -/
lemma IsMarked.not_dvd_M_mul_N (h : D.IsMarked Λ) : ¬p ∣ D.M ∧ p ≠ D.N ∧ ¬p ∣ D.M * D.N :=
  h.isSmallNonsplit.not_dvd_M_mul_N

/-- If `Λ` is a marked set above `p`, multiplying a place by the place named by `-p` conjugates the
induced prime, because `p` is inert in `K`. -/
lemma IsMarked.inducedPlace_placeOfInt_neg_mul (h : D.IsMarked Λ) (σ : D.Φ) :
    inducedPlace (D.placeOfInt (-p) * σ) = star (inducedPlace σ) := by
  simpa using D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one odd_one σ

/-- For a marked set `Λ` and odd `e`, multiplication by the place named by `-p ^ e` carries the
places whose conjugate induced prime lies in `Λ` onto the places whose induced prime lies in `Λ`. -/
lemma IsMarked.neg_pow_mul_mem_placesInducing_iff (h : D.IsMarked Λ) {e : ℕ} (he : Odd e)
    (σ : D.Φ) :
    D.placeOfInt (-p ^ e) * σ ∈ placesInducing Λ ↔ σ ∈ placesInducingConj Λ := by
  simp [D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he]

/-- For a marked set `Λ` and odd `e`, multiplication by the place named by `-p ^ e` carries the
places whose induced prime lies in `Λ` onto the places whose conjugate induced prime lies in `Λ`. -/
lemma IsMarked.neg_pow_mul_mem_placesInducingConj_iff (h : D.IsMarked Λ) {e : ℕ} (he : Odd e)
    (σ : D.Φ) :
    D.placeOfInt (-p ^ e) * σ ∈ placesInducingConj Λ ↔ σ ∈ placesInducing Λ := by
  simp [D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he]

/-- Let `Λ` be a marked set of primes of `E`: in particular each prime of `Λ` is induced by an
a-place, and `p` is exceptional, so it is inert in `K` and `-p` has odd order modulo `q₀`. If
`inducedPlace σ` or its conjugate lies in `Λ`, then `σ` is not a b-place. -/
lemma IsMarked.notMem_bPlaces (h : D.IsMarked Λ) (σ : D.Φ)
    (hσ : inducedPlace σ ∈ Λ ∨ star (inducedPlace σ) ∈ Λ) : σ ∉ D.bPlaces := by
  intro h_bPlace
  -- An a-place induces the prime of `σ` or its conjugate, so it lies on the orbit of `σ` under
  -- `-p`.
  obtain ⟨τ, h_aPlace, h_ind⟩ : ∃ τ ∈ D.aPlaces,
      inducedPlace τ = inducedPlace σ ∨ inducedPlace τ = star (inducedPlace σ) := by
    grind [h.induced_by_aPlace]
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, τ = D.placeOfInt (-p) ^ i * σ :=
    (inducedPlace_eq_or_star_iff h.isExceptional.chiK_eq_neg_one τ σ).1 h_ind
  -- Modulo `q₀` an a-place has class `1` and a b-place has class `-1`, so `(-p) ^ i ≡ -1`.
  set c : (ZMod P.q₀)ˣ := P.placeClass (P.q₀.dvd_mul_right _) (D.placeOfInt (-p))
  have h_neg : -c ^ i = 1 := by
    simpa [aPlaces, placeClass_of_mem_bPlaces, h_bPlace, c] using h_aPlace
  -- Raising this to the odd order `o₀` of `-p` gives `1 ≡ -1` modulo `q₀`.
  have h_order : c ^ D.o₀ p = 1 := by rw [o₀, pow_orderOf_eq_one]
  have h_eq : (1 : (ZMod P.q₀)ˣ) = -1 :=
    calc (1 : (ZMod P.q₀)ˣ) = (-c ^ i) ^ D.o₀ p := by rw [h_neg, one_pow]
      _ = -(c ^ D.o₀ p) ^ i := by rw [h.isExceptional.odd_o₀.neg_pow, pow_right_comm]
      _ = -1 := by rw [h_order, one_pow]
  exact P.d_pow_ne_neg_one 0 (by simpa using congrArg Units.val h_eq)

/-- At a place whose induced prime, or its conjugate, lies in a marked set, the weight is `a / x₁`,
because such a place is not a b-place. -/
lemma IsMarked.cast_weight_eq (h : D.IsMarked Λ) (σ : D.Φ)
    (hσ : inducedPlace σ ∈ Λ ∨ star (inducedPlace σ) ∈ Λ) :
    (D.weight σ : ℝ) = D.a / D.x₁ := by
  rw [cast_weight, ite_eq_right (h.notMem_bPlaces σ hσ)]

open scoped Classical in
/-- Let `l` be a prime of a set `Λ` that is marked: it is disjoint from its conjugate, its primes
are induced by a-places, and `p < x₁` is exceptional. For any function `G`, the sum of
`G (D.liftWeight j τ)` over the places `τ` that induce `l` equals the sum over the places that
induce the conjugate of `l`. Here `D.liftWeight j τ = D.weight τ + (j + 1/2) D.gap` is the weight at
`τ` of the character of the `j`-th lift in the chain. -/
lemma IsMarked.sum_inducedPlace_eq_sum_star (h : D.IsMarked Λ) (hl : l ∈ Λ) (j : ℕ) (G : ℕ → ℝ) :
    ∑ τ : D.Φ with inducedPlace τ = l, G (D.liftWeight j τ) =
      ∑ τ : D.Φ with inducedPlace τ = star l, G (D.liftWeight j τ) := by
  -- Multiplication by the place named by `-p` carries the places inducing `l` onto those inducing
  -- its conjugate.
  refine sum_equiv (.mulLeft (D.placeOfInt (-p)))
    (fun τ ↦ by simp [h.inducedPlace_placeOfInt_neg_mul]) fun τ hτ ↦ ?_
  have h_mem : inducedPlace τ ∈ Λ := by rwa [(mem_filter.1 hτ).2]
  -- Both `τ` and `-p τ` have the weight `a / x₁`.
  have h_weight : (D.weight τ : ℝ) = D.weight (D.placeOfInt (-p) * τ) := by
    simp [h.cast_weight_eq, h.inducedPlace_placeOfInt_neg_mul, h_mem]
  simp [liftWeight_eq, Nat.cast_injective h_weight]

open scoped Classical in
/-- Let the set `Λ` of primes of `E` be marked: it is disjoint from its conjugate, its primes are
induced by a-places, and `p < x₁` is exceptional. Let `w_j(τ) = D.liftWeight j τ` be the weight at
`τ` of the character of the `j`-th lift. For any function `G` of a weight and a prime, the sum of
`G (w_j(τ), 𝔩)` over the places `τ` whose induced prime `𝔩` lies in `Λ` (`placesInducing Λ`) equals
the sum of `G (w_j(τ), 𝔩̄)` over the places `τ` for which the conjugate `𝔩̄` of the induced prime
lies in `Λ`. -/
lemma IsMarked.sum_placesInducing_eq_sum_placesInducingConj (h : D.IsMarked Λ) (j : ℕ)
    (G : ℕ → FinPlace D.E → ℝ) :
    ∑ τ ∈ placesInducing Λ, G (D.liftWeight j τ) (inducedPlace τ) =
      ∑ τ ∈ placesInducingConj Λ, G (D.liftWeight j τ) (star (inducedPlace τ)) := by
  -- Group each sum by the prime of `Λ` that occurs, and use the balance at that prime.
  have h_group (f : D.Φ → FinPlace D.E) :
      ∑ τ : D.Φ with f τ ∈ Λ, G (D.liftWeight j τ) (f τ) =
        ∑ l ∈ Λ, ∑ τ : D.Φ with f τ = l, G (D.liftWeight j τ) l := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  rw [h_group, h_group fun τ ↦ star (inducedPlace τ)]
  refine sum_congr rfl fun l hl ↦ ?_
  simp [h.sum_inducedPlace_eq_sum_star hl j fun c ↦ G c l,
    star_eq_iff_star_eq (r := inducedPlace _), eq_comm (a := star l)]

open scoped Classical in
/-- The balance `IsMarked.sum_placesInducing_eq_sum_placesInducingConj` as one sum over all infinite
places `τ`: with `𝔩 = inducedPlace τ`, add `G (D.liftWeight j τ) 𝔩` if `𝔩 ∈ Λ` and subtract
`G (D.liftWeight j τ) (star 𝔩)` if `star 𝔩 ∈ Λ`. The total is zero. -/
lemma IsMarked.sum_inducedPlace_sub_star_eq_zero (h : D.IsMarked Λ) (j : ℕ)
    (G : ℕ → FinPlace D.E → ℝ) :
    ∑ τ : D.Φ, ((if inducedPlace τ ∈ Λ then G (D.liftWeight j τ) (inducedPlace τ) else 0) -
      (if star (inducedPlace τ) ∈ Λ then G (D.liftWeight j τ) (star (inducedPlace τ)) else 0)) =
        0 := by
  simp [sum_sub_distrib, ← sum_filter, h.sum_placesInducing_eq_sum_placesInducingConj j G]

/-- A prime of a marked set lies above `p`. -/
lemma IsMarked.natCast_mem_asIdeal (h : D.IsMarked Λ) (hl : l ∈ Λ) : ↑p ∈ l.asIdeal := by
  obtain ⟨τ, -, rfl⟩ := h.induced_by_aPlace l hl
  exact D.p_mem_inducedPlace τ

/-- For a marked set `Λ` (`D.IsMarked Λ`) and `l ∈ Λ`, `p` is a uniformiser at `l`: its `l`-adic
valuation is `exp (-1)`. The reason is that the prime `p` of a marked set divides neither `q₁` nor
`d`. -/
lemma IsMarked.valuation_natCast_eq_exp_neg_one (h : D.IsMarked Λ) (hl : l ∈ Λ) :
    l.valuation D.E p = WithZero.exp (-1) := by
  -- `l` lies above `p`, which is inert in `K` and so does not divide `q₁ * d`: it is unramified.
  rw [← map_natCast (algebraMap (NumberField.RingOfIntegers D.E) D.E), l.valuation_of_algebraMap]
  exact intValuation_natCast_eq_exp_neg_one (h.natCast_mem_asIdeal hl)
    (not_dvd_q₁_mul_d_of_inert h.isExceptional.chiK_eq_neg_one)

/-- Every prime `l` of a marked set `Λ` (disjoint from its complex conjugate, each prime induced by
an a-place) is split (`l.IsSplit`): `l` differs from its complex conjugate. -/
lemma IsMarked.isSplit (h : D.IsMarked Λ) (hl : l ∈ Λ) : l.IsSplit :=
  fun h_eq : star l = l ↦ h.star_notMem l hl (by rwa [h_eq])

/-- Let `Λ` be a marked set of primes of `E` above `p` and `l ∈ Λ`. In the finite adelic unitary
group with basis indexed by `D.X 0`, the group `maxCompactAt (D.X 0) l` of elements of the standard
maximal compact subgroup that are trivial away from `l` and `star l` lies in `D.levelX 0`, the level
that fixes the forms of `D.SourceForm`. -/
lemma IsMarked.maxCompactAt_le_levelX (h : D.IsMarked Λ) (hl : l ∈ Λ) :
    maxCompactAt (D.X 0) l ≤ D.levelX 0 := by
  -- Neither `l` nor its conjugate contains `piM * piN`, whose norm `M * N` is prime to `p`.
  have h_notMem (v : FinPlace D.E) (hv : ↑p ∈ v.asIdeal) : D.piM * D.piN ∉ v.asIdeal := by
    intro h_mem
    have h_norm : ((D.M * D.N : ℕ) : NumberField.RingOfIntegers D.E) ∈ v.asIdeal := by
      rw [Nat.cast_mul, ← piM_mul_star, ← piN_mul_star, mul_mul_mul_comm]
      exact v.asIdeal.mul_mem_right _ h_mem
    obtain ⟨-, -, h_ndvd⟩ := h.not_dvd_M_mul_N
    exact h_ndvd ((v.natCast_mem_iff_dvd hv).1 h_norm)
  have h_le : maxCompactAt (D.X 0) l ≤ principalLevel (D.X 0) (D.piM * D.piN) := by
    refine inf_supportedOn_le_principalLevel fun w hw ↦ ?_
    obtain rfl : w = l := hw
    exact ⟨h_notMem w (h.natCast_mem_asIdeal hl),
      h_notMem (star w) (by simpa [mem_star_place] using h.natCast_mem_asIdeal hl)⟩
  exact h_le.trans (D.principalLevel_le_levelX 0)

/-- The operator `p ^ A_𝔩 • T_{𝔩,𝔯}` on `D.SourceForm`, as an endomorphism over `embValRing`; here
`T_{𝔩,𝔯}` is the Hecke operator at the marked prime `𝔩` of index `𝔯 = D.ceilLogLifts p`, which
preserves `D.SourceForm`. -/
noncomputable def IsMarked.scaledHeckeOperator (h : D.IsMarked Λ) (l : Λ) :
    Module.End embValRing D.SourceForm :=
  LinearMap.restrictScalars embValRing <|
    (p : ℂ) ^ heckeScalingExponent l.1 •
      (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) (h.isSplit l.2)
        (D.ceilLogLifts p)).restrict
        fun _ hv ↦
          -- a vector of level `D.levelX 0` is spherical at `l`, by
          -- `maxCompactAt_le_levelX`
          heckeSplit_mem_levelSpace _ (D.ceilLogLifts p)
            (levelSpace_anti (h.maxCompactAt_le_levelX l.2) hv) IsLevel.le hv

/-! ### Collisions and full marks -/

/-- Let `Λ` be a full mark: a marked set that contains, for each a-place, the induced prime or its
conjugate. A collision outside `placesInducing Λ` is a pair `(τ, e)` with `e` odd such that `τ` and
its product with the place `D.placeOfInt (-p ^ e)` are a-places that induce no prime of `Λ`. Then
`collisionSum`, the sum of `D.a / p ^ e` over these collisions, is zero. -/
lemma IsFullMark.collisionSum_placesInducing_eq_zero (h : D.IsFullMark Λ) :
    D.collisionSum p (placesInducing Λ) = 0 := by
  -- In a collision `(τ, e)` the a-place `τ` induces no prime of `Λ`, so it induces the conjugate of
  -- one. As `e` is odd, the partner `-p ^ e τ` then induces a prime of `Λ`: there is no collision.
  have h_none (τ : D.Φ) (e : ℕ) : ¬D.IsCollision p (placesInducing Λ) τ e := by
    intro hc
    obtain ⟨-, h_odd, -⟩ := hc.ne_and_odd_and_dvd
    obtain ⟨-, hτ, h_partner⟩ := hc
    obtain ⟨h_aPlace, h_notMem⟩ : τ ∈ D.aPlaces ∧ τ ∉ placesInducing Λ := mem_sdiff.1 hτ
    have h_conj : τ ∈ placesInducingConj Λ := by
      simpa using (h.mem_or_star_mem τ h_aPlace).resolve_left (by simpa using h_notMem)
    exact notMem_sdiff_of_mem_right
      ((h.toIsMarked.neg_pow_mul_mem_placesInducing_iff h_odd τ).2 h_conj) h_partner
  simp [collisionSum, h_none]

end MarkedPrimes

/-! ## The cost of the low columns at the places inducing `Λ` -/

section LowColumns

open Finset Real Nat

variable {P : Parameters} {D : Data P} {p : ℕ} [q : Fact p.Prime] {j : ℕ}

/-- Let `j < m`, the number of lifts, and let the set `Λ` of primes of `E` be marked: it is disjoint
from its conjugate, its primes are induced by a-places, and `p < x₁` is exceptional. Let `L` be the
number of low columns, those of height below the rank `n_{j+1}` and other than `1`, in the diagrams
`D.columnCount` at the places that induce a prime of `Λ`. Let `r = ceilLogLifts p` be least with
`m ≤ p ^ r`, and `ν_p = transferExponent p = r f (n_m + r)`, where `f` is the number of infinite
places and `n_i = D.n i`. Then `#Λ ν_p + r L` is at most `loss p / m`, plus `a / x₁` for each
a-place inducing a prime of `Λ`. Here `a = x b` is the product of two scales of the data, and
`loss p` is `f a (log b)² / p`, times `m` if `p ≡ ±1` modulo `m`. -/
lemma IsMarked.card_mul_transferExponent_add_sum_lowColumns_le (hj : j < D.m) [PadicPlace p]
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) :
    #Λ * D.transferExponent p + D.ceilLogLifts p * ∑ σ ∈ placesInducing Λ, D.lowColumns j σ ≤
      D.loss p / D.m + #(D.aPlaces ∩ placesInducing Λ) * (D.a / D.x₁) := by
  -- The size of `p < x₁`, as an instance for `D.le_of_hasLogBound`.
  have hp_size : D.HasLogUpper p D.logX₁ :=
    D.hasLogUpper_of_le_of_nonneg hΛ.isSmallNonsplit.1.le p.cast_nonneg
  have hp : 0 < p := q.1.pos
  have h_place (σ : D.Φ) (hσ : σ ∈ placesInducing Λ) :
      D.ceilLogLifts p * (D.lowColumns j σ : ℝ) ≤ D.a / p / D.m + ite (σ ∈ D.aPlaces) (D.a / D.x₁)
        0 := by
    obtain ⟨h_inert, -, h_odd, h_order⟩ := hΛ.isExceptional
    -- A place inducing a prime of `Λ` is not a b-place, so it has about `a / x₁` low columns.
    grw [lowColumns_le hj σ, hΛ.cast_weight_eq σ (.inl (by simpa using hσ))]
    obtain hpm | hmp := le_total p D.m
    · grw [hpm]
      split <;> simpa using D.le_of_hasLogBound
    · -- Here `ceilLogLifts p = 1`, so the odd number `o₀ p ≤ ceilLogLifts p` is `1`: the orbit of
      -- the a-place that induces `inducedPlace σ` under `-p` consists of a-places, and `σ` lies on
      -- it.
      have h_one : D.ceilLogLifts p = 1 := clog_eq_one D.nat_le_of_hasLogBound hmp
      have h_aPlace : σ ∈ D.aPlaces := by
        grind [inducedPlace_eq_or_star_iff, hΛ.induced_by_aPlace, aPlaces, one_pow, o₀,
          orderOf_eq_one_iff]
      grw [h_one, ite_eq_left h_aPlace, add_comm]
      simpa using D.le_of_hasLogBound
  grw [cast_sum, mul_sum, sum_le_sum h_place, ← le_loss, hΛ.card_le, transferExponent]
  -- What remains once the sums over the a-places cancel holds by orders of magnitude.
  suffices (D.f ^ 2 * D.ceilLogLifts p * (D.n D.m + D.ceilLogLifts p) * p +
      #(placesInducing Λ) * D.a / D.m : ℝ) ≤ D.f * D.a * D.logB ^ 2 / D.m by
    simpa [inter_comm, ← add_assoc, sum_add_distrib, field]
  exact D.le_of_hasLogBound

end LowColumns

end New.Data

end
