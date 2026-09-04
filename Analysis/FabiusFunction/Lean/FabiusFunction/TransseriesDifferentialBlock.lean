import FabiusFunction.TransseriesBlockAntiderivative
import Mathlib.Algebra.Polynomial.Derivation

/-!
# How the derivation acts on a block

The computational heart of the polynomial–logarithmic calculus, proved
here in the generality the argument actually uses: **any** commutative
ring carrying a derivation `d` and two elements `t`, `L` with

`d t = -t²`,  `d L = t`

(the abstract shape of `t = X⁻¹`, `L = log X`).  On the block
`tⁿ·K[L]` the derivation acts as

`d (tⁿ·p(L)) = t^(n+1)·((∂_L - n)p)(L)`,

so it is `t^(n+1)` times the **block operator** of
`TransseriesBlockAntiderivative` at `c = n`.  This is the identity that
turns antidifferentiation of a transseries into the inversion of
`∂_L - c` block by block, and it explains the resonance: `n = 0` is
exactly the block where that operator fails to be invertible.

Nothing here needs the ring `K[t,t⁻¹][L]` to be constructed; every
differential ring containing such a `t` and `L` obeys the law, and the
concrete ring is one model of it.

* `derivation_pow_t` — `d (tⁿ) = -n·t^(n+1)` for natural powers.
* `derivation_block` — **the natural-power block law**.
* `derivation_zpow_block` — the source-shaped block law for every
  integer Laurent exponent, in an ambient field where `t ≠ 0`.
* `exists_block_primitive` — **antidifferentiation inside a nonresonant
  block**: for `n ≠ 0` in the base field every `t^(n+1)·p(L)` is `d` of
  some `tⁿ·q(L)`, with `q` given explicitly by the Neumann sum.
* `exists_zpow_block_primitive` — the Laurent version in the source's
  indexing: if `n ≠ 1`, then `tⁿ·p(L)` has a primitive of the form
  `t^(n-1)·q(L)`, with the same logarithmic degree.
* `existsUnique_zpow_block_primitive` — uniqueness of that polynomial
  primitive when evaluation at `L` is injective.
* `derivation_block_zero`, `exists_block_primitive_resonant` — the
  resonant block `n = 0`, where the primitive still exists but its
  logarithmic degree is one higher.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (d : Derivation K A A) {t L : A}

/-- `d (tⁿ) = -n·t^(n+1)`, the derivation's action on the power part of
a block.  At `n = 0` both sides vanish. -/
theorem derivation_pow_t (hdt : d t = -t ^ 2) (n : ℕ) :
    d (t ^ n) = -(n : A) * t ^ (n + 1) := by
  rcases n with _ | m
  · simp
  · rw [d.leibniz_pow, hdt, Nat.add_sub_cancel]
    push_cast
    simp only [smul_eq_mul, smul_neg, mul_neg]
    ring

/-- **The block law.**  On the block `tⁿ·K[L]` the derivation is
`t^(n+1)` times the block operator `∂_L - n`:

`d (tⁿ·p(L)) = t^(n+1)·((∂_L - n)p)(L)`. -/
theorem derivation_block (hdt : d t = -t ^ 2) (hdL : d L = t) (n : ℕ)
    (p : K[X]) :
    d (t ^ n * aeval L p) =
      t ^ (n + 1) * aeval L (blockOperator (n : K) p) := by
  have hchain : d (aeval L p) = aeval L (derivative p) • d L :=
    d.comp_aeval_eq L p
  rw [d.leibniz, hchain, hdL, derivation_pow_t d hdt n, blockOperator,
    map_sub, map_mul, aeval_C, map_natCast]
  simp only [smul_eq_mul]
  ring

/-! ## Laurent blocks -/

/-- **The integer-power block law.**  In an ambient field, for nonzero `t` and
every `n : ℤ`,

`d (tⁿ·p(L)) = t^(n+1)·((∂_L - n)p)(L)`.

The field assumption is exactly the setting of `Derivation.leibniz_zpow`; the
coefficient ring of the logarithmic polynomial may be any commutative ring. -/
theorem derivation_zpow_block {R B : Type*} [CommRing R] [Field B] [Algebra R B]
    (d : Derivation R B B) {t L : B} (ht : t ≠ 0) (hdt : d t = -t ^ 2)
    (hdL : d L = t) (n : ℤ) (p : R[X]) :
    d (t ^ n * aeval L p) =
      t ^ (n + 1) * aeval L (blockOperator (n : R) p) := by
  have hchain : d (aeval L p) = aeval L (derivative p) • d L :=
    d.comp_aeval_eq L p
  rw [d.leibniz, d.leibniz_zpow, hchain, hdt, hdL, blockOperator,
    map_sub, map_mul, aeval_C, map_intCast]
  simp only [smul_eq_mul, zsmul_eq_mul]
  rw [← zpow_natCast t 2]
  have hpow_one : t ^ n * t = t ^ (n + 1) := by
    simpa only [zpow_one] using (zpow_add₀ ht n 1).symm
  have hpow_two : t ^ (n - 1) * t ^ (2 : ℤ) = t ^ (n + 1) := by
    calc
      t ^ (n - 1) * t ^ (2 : ℤ) = t ^ ((n - 1) + 2) :=
        (zpow_add₀ ht (n - 1) 2).symm
      _ = t ^ (n + 1) := by
        congr 1
        ring
  calc
    t ^ n * (aeval L (derivative p) * t) +
        aeval L p * ((n : B) * (t ^ (n - 1) * -t ^ (2 : ℤ))) =
      (t ^ n * t) * aeval L (derivative p) -
        (n : B) * (t ^ (n - 1) * t ^ (2 : ℤ)) * aeval L p := by ring
    _ = t ^ (n + 1) *
        (aeval L (derivative p) - (n : B) * aeval L p) := by
      rw [hpow_one, hpow_two]
      ring

/-- **Nonresonant Laurent-block antidifferentiation.**  In the source's
indexing, if `n ≠ 1`, every `tⁿ·p(L)` has a primitive of the shape
`t^(n-1)·q(L)`, and `q` has the same logarithmic degree as `p`.

Existence and degree preservation use the bijectivity of
`blockOperator ((n - 1 : ℤ) : F)`. -/
theorem exists_zpow_block_primitive {F B : Type*} [Field F] [CharZero F]
    [Field B] [Algebra F B] (d : Derivation F B B) {t L : B} (ht : t ≠ 0)
    (hdt : d t = -t ^ 2) (hdL : d L = t) {n : ℤ} (hn : n ≠ 1)
    (p : F[X]) :
    ∃ q : F[X], q.natDegree = p.natDegree ∧
      d (t ^ (n - 1) * aeval L q) = t ^ n * aeval L p := by
  have hc : ((n - 1 : ℤ) : F) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr hn)
  obtain ⟨q, hq⟩ := (blockOperator_bijective hc).2 p
  refine ⟨q, ?_, ?_⟩
  · calc
      q.natDegree = (blockOperator ((n - 1 : ℤ) : F) q).natDegree :=
        (natDegree_blockOperator hc q).symm
      _ = p.natDegree := congrArg Polynomial.natDegree hq
  · have h := derivation_zpow_block d ht hdt hdL (n - 1) q
    rw [hq] at h
    simpa only [sub_add_cancel] using h

/-- **Uniqueness of the nonresonant Laurent-block primitive.**  If evaluation
at `L` is injective (as it is when `L` is transcendental over `F`), then the
polynomial `q` in `exists_zpow_block_primitive` is unique.  The explicit
injectivity hypothesis is necessary in the abstract ambient-field model:
without it distinct polynomials can represent the same element at `L`. -/
theorem existsUnique_zpow_block_primitive {F B : Type*} [Field F] [CharZero F]
    [Field B] [Algebra F B] (d : Derivation F B B) {t L : B} (ht : t ≠ 0)
    (hdt : d t = -t ^ 2) (hdL : d L = t)
    (hL : Function.Injective (aeval L : F[X] → B)) {n : ℤ} (hn : n ≠ 1)
    (p : F[X]) :
    ∃! q : F[X], q.natDegree = p.natDegree ∧
      d (t ^ (n - 1) * aeval L q) = t ^ n * aeval L p := by
  have hc : ((n - 1 : ℤ) : F) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr hn)
  obtain ⟨q, hq⟩ := (blockOperator_bijective hc).2 p
  refine ⟨q, ?_, ?_⟩
  · constructor
    · calc
        q.natDegree = (blockOperator ((n - 1 : ℤ) : F) q).natDegree :=
          (natDegree_blockOperator hc q).symm
        _ = p.natDegree := congrArg Polynomial.natDegree hq
    · have h := derivation_zpow_block d ht hdt hdL (n - 1) q
      rw [hq] at h
      simpa only [sub_add_cancel] using h
  · intro q' hq'
    apply (blockOperator_bijective hc).1
    apply hL
    have hq'_block := derivation_zpow_block d ht hdt hdL (n - 1) q'
    rw [sub_add_cancel] at hq'_block
    rw [hq]
    exact mul_left_cancel₀ (zpow_ne_zero n ht) (hq'_block.symm.trans hq'.2)

/-- **Antidifferentiation inside a nonresonant block.**  When `n ≠ 0` in
the base field, every element `t^(n+1)·p(L)` of a block is the derivative
of an element `tⁿ·q(L)` of the block below, with `q` the explicit Neumann
sum of `TransseriesBlockAntiderivative`.  At `n = 0` this fails — that is
the resonant block, where a logarithm has to be created. -/
theorem exists_block_primitive {F : Type*} [Field F] [Algebra F A]
    (d : Derivation F A A) {t L : A} (hdt : d t = -t ^ 2) (hdL : d L = t)
    {n : ℕ} (hn : (n : F) ≠ 0) (p : F[X]) :
    d (t ^ n * aeval L (blockAntiderivative (n : F) p)) =
      t ^ (n + 1) * aeval L p := by
  rw [derivation_block d hdt hdL n, blockOperator_blockAntiderivative hn]

/-- The block law at `n = 0`: `d (p(L)) = t·p'(L)`, the statement that
`L` differentiates to `t` extended from `L` to every polynomial in it. -/
theorem derivation_block_zero (hdL : d L = t) (p : K[X]) :
    d (aeval L p) = t * aeval L (derivative p) := by
  rw [d.comp_aeval_eq, hdL]
  simp only [smul_eq_mul]
  ring

/-- **Antidifferentiation at the resonant block.**  The block law at
`n = 0` says `d` restricted to `K[L]` is `t·∂_L`, and `∂_L` is surjective
over a characteristic zero field, so every `t·p(L)` still has a primitive
— but the primitive is `resonantAntiderivative p`, whose logarithmic
degree is one higher than `p`'s (`natDegree_resonantAntiderivative`).
This is the sense in which the resonant block creates a logarithm: the
antiderivative exists, but not inside the same logarithmic degree. -/
theorem exists_block_primitive_resonant {F : Type*} [Field F] [CharZero F]
    [Algebra F A] (d : Derivation F A A) {t L : A} (hdL : d L = t) (p : F[X]) :
    d (aeval L (resonantAntiderivative p)) = t * aeval L p := by
  rw [derivation_block_zero d hdL, derivative_resonantAntiderivative]

end Fabius
