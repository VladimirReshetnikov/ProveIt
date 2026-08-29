import FabiusFunction.GeneralizedZeroDivisor
import FabiusFunction.LobeSignNegative

/-!
# The lobe-sign law on the whole real axis

The volume's sign law `sgn Φ_a(x) = ε_a(⌊x⌋)` is proved in the corpus
in pieces, each with its own hypothesis:

* `LobeSignLaw` — on an open lobe, `N < x < N + 1`;
* `CanonicalIntegerPoint` — at an integer whose multiplicity vanishes,
  and separately at `x = 0`;
* `LobeSignNegative` — the reflections of both.

Each header records that the others are missing, and `LobeSignLaw`
says outright that "the behaviour of `Φ_a` *at* an integer is not
addressed".  This module assembles them into one statement covering
every real point, using the last ingredient that was missing: the
complete zero set, from `GeneralizedZeroDivisor`.

The law holds everywhere it can, and the exceptions are exactly the
zeros, which are known:

`Ψ_a(x) = 0` **or** `0 < ε_a(⌊|x|⌋) · Ψ_a(x)`,  for every `x : ℝ`,

and the first alternative happens exactly when `|x|` is a positive
integer of nonzero multiplicity
(`canonicalRealProduct_eq_zero_iff_of_nonneg`).  There is no third
possibility and no gap: `x = 0` is covered (both `ε_a(0)` and
`Ψ_a(0)` are `1`), integer points of vanishing multiplicity are
covered, and non-integer points are covered by the open-lobe law.

The index is `⌊|x|⌋`, not `⌊x⌋`.  On `-(N+1) < x < -N` the reflected
point lies in the lobe `(N, N+1)`, so the sign is `ε_a(N)`, and
`⌊x⌋ = -(N+1)` is not even a natural number.  This is the same
correction `LobeSignNegative` records; the volume writes `⌊x⌋`
because it has `x ≥ 0` in mind.

* `Fabius.canonicalRealProduct_eq_zero_iff_of_nonneg` — **the zero
  set of the real product** on `[0, ∞)`;
* `Fabius.parityCharacter_mul_canonicalRealProduct_nonneg_dichotomy` —
  **the law on `[0, ∞)`**;
* `Fabius.parityCharacter_mul_canonicalRealProduct_dichotomy` — **the
  law on all of `ℝ`**, indexed by `⌊|x|⌋`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The zero set of the real product -/

/-- **Where `Ψ_a` vanishes on `[0, ∞)`**: exactly at the positive
integers of nonzero multiplicity.

This is `generalizedRvachevProduct_eq_zero_iff_int` transported along
the real bridge `generalizedRvachevProduct_ofReal_eq_canonicalRealProduct`.
The point `x = 0` is not an exception to be argued around — it is
excluded by `1 ≤ m`, and correctly so, since `Ψ_a(0) = 1`. -/
theorem canonicalRealProduct_eq_zero_iff_of_nonneg (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {x : ℝ}
    (hx : 0 ≤ x) :
    canonicalRealProduct a x = 0 ↔
      ∃ m : ℕ, 1 ≤ m ∧ x = (m : ℝ) ∧
        weightedScaleMultiplicity 2 a m ≠ 0 := by
  have hbridge :
      generalizedRvachevProduct a ((x : ℝ) : ℂ)
        = ((canonicalRealProduct a x : ℝ) : ℂ) :=
    generalizedRvachevProduct_ofReal_eq_canonicalRealProduct a ha x
  constructor
  · intro hzero
    have hc : generalizedRvachevProduct a ((x : ℝ) : ℂ) = 0 := by
      rw [hbridge, hzero, Complex.ofReal_zero]
    obtain ⟨n, hn0, hxn, hmult⟩ :=
      (generalizedRvachevProduct_eq_zero_iff_int a ha _).mp hc
    have hxr : x = ((n : ℤ) : ℝ) := by exact_mod_cast hxn
    have hnpos : 0 < n := by
      rcases lt_trichotomy n 0 with hneg | rfl | hpos
      · exfalso
        have : ((n : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
        linarith [hxr ▸ hx]
      · exact absurd rfl hn0
      · exact hpos
    refine ⟨n.natAbs, ?_, ?_, hmult⟩
    · omega
    · rw [hxr]
      congr 1
      omega
  · rintro ⟨m, hm1, rfl, hmult⟩
    have hc : generalizedRvachevProduct a (((m : ℕ) : ℝ) : ℂ) = 0 := by
      refine (generalizedRvachevProduct_eq_zero_iff_int a ha _).mpr
        ⟨(m : ℤ), by omega, by push_cast; ring, ?_⟩
      simpa using hmult
    rw [hbridge] at hc
    exact_mod_cast hc

/-! ## The law on the whole axis -/

/-- **The sign law on `[0, ∞)`**, with no hypothesis beyond `x ≥ 0`:
either `Ψ_a(x) = 0`, or the volume's sign law holds at `x` with index
`⌊x⌋`.

The three cases are the three pieces the corpus already had.  At a
non-integer point `⌊x⌋ < x < ⌊x⌋ + 1` and the open-lobe law applies;
at a positive integer of vanishing multiplicity the integer-point law
applies; at a positive integer of nonzero multiplicity the product
vanishes; and `x = 0` is the residue `Ψ_a(0) = ε_a(0) = 1`. -/
theorem parityCharacter_mul_canonicalRealProduct_nonneg_dichotomy
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {x : ℝ} (hx : 0 ≤ x) :
    canonicalRealProduct a x = 0 ∨
      0 < ((parityCharacter a ⌊x⌋₊ : ℤ) : ℝ) *
        canonicalRealProduct a x := by
  by_cases hint : x = (⌊x⌋₊ : ℝ)
  · -- an integer point
    by_cases hzero : ⌊x⌋₊ = 0
    · refine Or.inr ?_
      have hx0 : x = 0 := by rw [hint, hzero, Nat.cast_zero]
      subst hx0
      simp [canonicalRealProduct_zero_eq_one]
    · by_cases hm : weightedScaleMultiplicity 2 a ⌊x⌋₊ = 0
      · refine Or.inr ?_
        have h :=
          parityCharacter_mul_canonicalRealProduct_natCast_pos a ha hm
        rwa [← hint] at h
      · refine Or.inl ?_
        exact (canonicalRealProduct_eq_zero_iff_of_nonneg a ha hx).mpr
          ⟨⌊x⌋₊, Nat.one_le_iff_ne_zero.mpr hzero, hint, hm⟩
  · -- a non-integer point: it lies strictly inside its lobe
    refine Or.inr ?_
    have hlo : (⌊x⌋₊ : ℝ) < x :=
      lt_of_le_of_ne (Nat.floor_le hx) (Ne.symm hint)
    have hhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    exact parityCharacter_mul_canonicalRealProduct_pos a ha hlo hhi

/-- **The sign law on all of `ℝ`**, indexed by `⌊|x|⌋`.

Negative arguments are carried by evenness of `Ψ_a`
(`canonicalRealProduct_neg`), which is why the index is `⌊|x|⌋`: on
`-(N+1) < x < -N` the reflected point lies in `(N, N+1)`, and `⌊x⌋`
would be the negative integer `-(N+1)`. -/
theorem parityCharacter_mul_canonicalRealProduct_dichotomy (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (x : ℝ) :
    canonicalRealProduct a x = 0 ∨
      0 < ((parityCharacter a ⌊|x|⌋₊ : ℤ) : ℝ) *
        canonicalRealProduct a x := by
  have habs : canonicalRealProduct a |x| = canonicalRealProduct a x := by
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, canonicalRealProduct_neg]
  have h := parityCharacter_mul_canonicalRealProduct_nonneg_dichotomy
    a ha (abs_nonneg x)
  rwa [habs] at h

end Fabius
