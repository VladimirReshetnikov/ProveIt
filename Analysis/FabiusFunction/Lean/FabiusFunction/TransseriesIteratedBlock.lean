import FabiusFunction.TransseriesDifferentialBlock

/-!
# Repeated derivative of a coefficient block

The transseries volume's `plt:lem:om-repeated-derivative`: iterating the
block law of `TransseriesDifferentialBlock` `k` times gives

`D^k (tⁿ p(L)) = t^{n+k} · [∏_{j<k} (∂_L - n - j)] p(L)`,

so a block of inverse-power order `n` differentiated `k` times is a block
of order `n + k` whose polynomial has been hit by the *shifted falling
operator* `∏_{j<k}(∂_L - n - j)`.  This is the identity behind the
`α`-family of Part V: the coefficient blocks of `ω` and of its
derivatives are related by falling operators, which is why the Lambert
coefficient polynomials are themselves values of a falling-factorial
operator.

As in the block law itself, the statement is proved for any commutative
ring with a derivation `d` and elements `t, L` with `d t = -t²`,
`d L = t`; the concrete ring `K[t,t⁻¹][L]` is one model.

* `shiftOperator c k` — `∏_{j<k}(∂_L - c - j)`, built as `blockOperator`s.
* `iterate_derivation_block` — natural exponent `n`.
* `iterate_derivation_block_zpow` — integer exponent, `t` a unit.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

/-- The shifted falling operator `∏_{j<k} (∂_L - c - j)`, with the factor
`∂_L - c - (k-1)` applied last. -/
noncomputable def shiftOperator {R : Type*} [CommRing R] (c : R) : ℕ → R[X] → R[X]
  | 0, p => p
  | (k + 1), p => blockOperator (c + k) (shiftOperator c k p)

/-- The empty product is the identity. -/
@[simp] theorem shiftOperator_zero {R : Type*} [CommRing R] (c : R) (p : R[X]) :
    shiftOperator c 0 p = p := rfl

/-- One more factor, `∂_L - c - k`, applied last. -/
theorem shiftOperator_succ {R : Type*} [CommRing R] (c : R) (k : ℕ) (p : R[X]) :
    shiftOperator c (k + 1) p = blockOperator (c + k) (shiftOperator c k p) := rfl

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (d : Derivation K A A) {L : A}

/-- **Repeated derivative of a block, natural exponent.** -/
theorem iterate_derivation_block {t : A} (hdt : d t = -t ^ 2) (hdL : d L = t)
    (n k : ℕ) (p : K[X]) :
    (⇑d)^[k] (t ^ n * aeval L p) =
      t ^ (n + k) * aeval L (shiftOperator (n : K) k p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, derivation_block d hdt hdL (n + k),
        shiftOperator_succ, show n + (k + 1) = n + k + 1 by omega, Nat.cast_add]

/-- **Repeated derivative of a block** (`plt:lem:om-repeated-derivative`),
integer exponent: `D^k (tⁿ p(L)) = t^{n+k} · [∏_{j<k}(∂_L - n - j)] p(L)`. -/
theorem iterate_derivation_block_zpow {u : Aˣ} (hdt : d (u : A) = -(u : A) ^ 2)
    (hdL : d L = (u : A)) (n : ℤ) (k : ℕ) (p : K[X]) :
    (⇑d)^[k] (((u ^ n : Aˣ) : A) * aeval L p) =
      ((u ^ (n + k) : Aˣ) : A) * aeval L (shiftOperator (n : K) k p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, derivation_block_zpow d hdt hdL (n + k),
        shiftOperator_succ, show n + ((k + 1 : ℕ) : ℤ) = n + k + 1 by push_cast; ring,
        Int.cast_add, Int.cast_natCast]

end Fabius
