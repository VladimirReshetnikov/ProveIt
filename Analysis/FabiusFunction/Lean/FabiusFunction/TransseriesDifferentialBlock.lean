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

* `derivation_pow_t` — `d (tⁿ) = -n·t^(n+1)`.
* `derivation_block` — **the block law**.
* `successiveBlockOperator` — the commuting product
  `(∂_L-c-k+1)⋯(∂_L-c)` governing `k` successive derivatives.
* `derivation_iterate_block`, `derivation_iterate_block_zpow` — the
  **repeated block law**, respectively without and with negative powers.
* `exists_block_primitive` — **antidifferentiation inside a nonresonant
  block**: for `n ≠ 0` in the base field every `t^(n+1)·p(L)` is `d` of
  some `tⁿ·q(L)`, with `q` given explicitly by the Neumann sum.
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

/-! ## Successive block operators and repeated derivatives -/

/-- The successive block operator

`Δ(c, k) = (∂_L - c - (k-1)) ∘ ⋯ ∘ (∂_L - c)`.

The empty operator `Δ(c, 0)` is the identity.  Defining the product in
this order makes the recurrence which arises by taking one more derivative
definitional; commutativity of the factors is proved below.  The parameter
`c` is an arbitrary scalar, so this same operator applies to integral,
Puiseux, and Hahn exponents whenever their exponent group maps into the
coefficient ring. -/
noncomputable def successiveBlockOperator {R : Type*} [CommRing R]
    (c : R) : ℕ → R[X] → R[X]
  | 0, p => p
  | k + 1, p =>
      blockOperator (c + (k : R)) (successiveBlockOperator c k p)

/-- The length-zero successive block operator is the identity. -/
@[simp] theorem successiveBlockOperator_zero {R : Type*} [CommRing R]
    (c : R) (p : R[X]) :
    successiveBlockOperator c 0 p = p := rfl

/-- Appending the last factor gives
`Δ(c, k+1)p = (∂_L-c-k)(Δ(c,k)p)`. -/
theorem successiveBlockOperator_succ_last {R : Type*} [CommRing R]
    (c : R) (k : ℕ) (p : R[X]) :
    successiveBlockOperator c (k + 1) p =
      blockOperator (c + (k : R)) (successiveBlockOperator c k p) := rfl

/-- Any two scalar-shifted polynomial derivatives commute:
`(∂_L-a)(∂_L-b)p = (∂_L-b)(∂_L-a)p`. -/
theorem blockOperator_comm {R : Type*} [CommRing R] (a b : R) (p : R[X]) :
    blockOperator a (blockOperator b p) =
      blockOperator b (blockOperator a p) := by
  simp only [blockOperator, map_sub, Polynomial.derivative_C_mul]
  ring

/-- Every block operator commutes with every successive block operator. -/
theorem blockOperator_successiveBlockOperator {R : Type*} [CommRing R]
    (a c : R) (k : ℕ) (p : R[X]) :
    blockOperator a (successiveBlockOperator c k p) =
      successiveBlockOperator c k (blockOperator a p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [successiveBlockOperator_succ_last,
        successiveBlockOperator_succ_last, blockOperator_comm, ih]

/-- **Cocycle law for successive block operators.**  Splitting `k+ℓ`
successive factors after the first `k` shifts the starting scalar of the
remaining `ℓ` factors by `k`:

`Δ(c, k+ℓ)p = Δ(c+k, ℓ)(Δ(c,k)p)`. -/
theorem successiveBlockOperator_add {R : Type*} [CommRing R]
    (c : R) (k ℓ : ℕ) (p : R[X]) :
    successiveBlockOperator c (k + ℓ) p =
      successiveBlockOperator (c + (k : R)) ℓ
        (successiveBlockOperator c k p) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [Nat.add_succ, successiveBlockOperator_succ_last,
        successiveBlockOperator_succ_last, ih]
      congr 1
      push_cast
      ring

/-- Removing the first factor gives the manuscript's other recurrence
`Δ(c,k+1)p = Δ(c+1,k)((∂_L-c)p)`. -/
theorem successiveBlockOperator_succ_first {R : Type*} [CommRing R]
    (c : R) (k : ℕ) (p : R[X]) :
    successiveBlockOperator c (k + 1) p =
      successiveBlockOperator (c + 1) k (blockOperator c p) := by
  simpa [Nat.one_add, successiveBlockOperator] using
    successiveBlockOperator_add c 1 k p

/-- **Repeated block law for natural exponents.**  In any commutative
differential algebra with `d t = -t²` and `d L = t`, taking `k`
derivatives of `tⁿ p(L)` raises the outer exponent by `k` and applies the
successive operator `Δ(n,k)` to `p`.  No field or characteristic hypothesis
is needed, and `t` need not be a unit. -/
theorem derivation_iterate_block (hdt : d t = -t ^ 2) (hdL : d L = t)
    (n k : ℕ) (p : K[X]) :
    (d^[k]) (t ^ n * aeval L p) =
      t ^ (n + k) * aeval L (successiveBlockOperator (n : K) k p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa [successiveBlockOperator, Nat.cast_add, Nat.add_assoc] using
        derivation_block d hdt hdL (n + k)
          (successiveBlockOperator (n : K) k p)

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
theorem derivation_block_zero (hdt : d t = -t ^ 2) (hdL : d L = t)
    (p : K[X]) :
    d (aeval L p) = t * aeval L (derivative p) := by
  have h := derivation_block d hdt hdL 0 p
  simpa [blockOperator] using h

/-- **Antidifferentiation at the resonant block.**  The block law at
`n = 0` says `d` restricted to `K[L]` is `t·∂_L`, and `∂_L` is surjective
over a characteristic zero field, so every `t·p(L)` still has a primitive
— but the primitive is `resonantAntiderivative p`, whose logarithmic
degree is one higher than `p`'s (`natDegree_resonantAntiderivative`).
This is the sense in which the resonant block creates a logarithm: the
antiderivative exists, but not inside the same logarithmic degree. -/
theorem exists_block_primitive_resonant {F : Type*} [Field F] [CharZero F]
    [Algebra F A] (d : Derivation F A A) {t L : A} (hdt : d t = -t ^ 2)
    (hdL : d L = t) (p : F[X]) :
    d (aeval L (resonantAntiderivative p)) = t * aeval L p := by
  rw [derivation_block_zero d hdt hdL, derivative_resonantAntiderivative]

/-! ## Integer exponents: the Laurent form of the block law -/

/-- `t⁻¹` differentiates to `1`: with `t = X⁻¹` this is `dX/dX = 1`. -/
theorem derivation_val_inv {u : Aˣ} (hdt : d (u : A) = -(u : A) ^ 2) :
    d ((u⁻¹ : Aˣ) : A) = 1 := by
  have h : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := u.inv_mul
  rw [d.leibniz_of_mul_eq_one h, hdt]
  simp only [smul_eq_mul, mul_neg, neg_mul, neg_neg]
  rw [← mul_pow, u.inv_mul, one_pow]

/-- Powers of `t⁻¹`: `d ((t⁻¹)^m) = m·(t⁻¹)^(m-1)`, the ordinary power
rule for the variable `X = t⁻¹`. -/
theorem derivation_pow_inv {u : Aˣ} (hdt : d (u : A) = -(u : A) ^ 2)
    (m : ℕ) :
    d (((u⁻¹ : Aˣ) : A) ^ m) = (m : A) * ((u⁻¹ : Aˣ) : A) ^ (m - 1) := by
  rw [d.leibniz_pow, derivation_val_inv d hdt]
  simp [nsmul_eq_mul]

/-- `d (tⁿ) = -n·t^(n+1)` for **integer** `n`, when `t` is a unit. -/
theorem derivation_zpow_t {u : Aˣ} (hdt : d (u : A) = -(u : A) ^ 2)
    (n : ℤ) :
    d ((u ^ n : Aˣ) : A) = -(n : A) * ((u ^ (n + 1) : Aˣ) : A) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 : ((u ^ (m : ℤ) : Aˣ) : A) = (u : A) ^ m := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    have h2 : ((u ^ ((m : ℤ) + 1) : Aˣ) : A) = (u : A) ^ (m + 1) := by
      rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, Units.val_pow_eq_pow_val]
    rw [h1, h2, derivation_pow_t d hdt m]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) :=
      ⟨(-n - 1).toNat, by omega⟩
    have h1 : ((u ^ (-((m : ℤ) + 1)) : Aˣ) : A) = ((u⁻¹ : Aˣ) : A) ^ (m + 1) := by
      rw [show (-((m : ℤ) + 1)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    have h2 : ((u ^ (-((m : ℤ) + 1) + 1) : Aˣ) : A) = ((u⁻¹ : Aˣ) : A) ^ m := by
      rw [show (-((m : ℤ) + 1) + 1) = -((m : ℕ) : ℤ) by omega,
        zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [h1, h2, derivation_pow_inv d hdt (m + 1), Nat.add_sub_cancel]
    push_cast
    ring

/-- **The block law with integer exponents** (`plt:eq:mot-block-derivative`):
for `n ∈ ℤ` and `p ∈ K[L]`,

`d (tⁿ·p(L)) = t^(n+1)·(p'(L) - n·p(L))`. -/
theorem derivation_block_zpow {u : Aˣ} (hdt : d (u : A) = -(u : A) ^ 2)
    (hdL : d L = (u : A)) (n : ℤ) (p : K[X]) :
    d (((u ^ n : Aˣ) : A) * aeval L p) =
      ((u ^ (n + 1) : Aˣ) : A) * aeval L (blockOperator (n : K) p) := by
  have hchain : d (aeval L p) = aeval L (derivative p) • d L :=
    d.comp_aeval_eq L p
  have e1 : ((u ^ (n + 1) : Aˣ) : A) = ((u ^ n : Aˣ) : A) * (u : A) := by
    rw [zpow_add_one, Units.val_mul]
  rw [d.leibniz, hchain, hdL, derivation_zpow_t d hdt n, blockOperator,
    map_sub, map_mul, aeval_C, map_intCast, e1]
  simp only [smul_eq_mul]
  ring

/-- **Repeated block law for every integer exponent.**  When `t` is a unit,
the natural-exponent formula extends without further hypotheses to all
`n : ℤ`:

`d^[k] (tⁿ p(L)) = t^(n+k) (Δ(n,k)p)(L)`.

This is the Laurent-polynomial instance of the manuscript's repeated
derivative formula. -/
theorem derivation_iterate_block_zpow {u : Aˣ}
    (hdt : d (u : A) = -(u : A) ^ 2) (hdL : d L = (u : A))
    (n : ℤ) (k : ℕ) (p : K[X]) :
    (d^[k]) (((u ^ n : Aˣ) : A) * aeval L p) =
      ((u ^ (n + (k : ℤ)) : Aˣ) : A) *
        aeval L (successiveBlockOperator (n : K) k p) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa [successiveBlockOperator, Nat.cast_add, Int.cast_add, Nat.add_assoc,
        add_assoc] using
        derivation_block_zpow d hdt hdL (n + (k : ℤ))
          (successiveBlockOperator (n : K) k p)

end Fabius
