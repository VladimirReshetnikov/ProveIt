import FabiusFunction.GeneralizedProuhetBlock
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.GeomSum

/-!
# The order of the zero at `z = 1` of a generalized Prouhet block

The exponent-sequence volume's generalized Prouhet theorem carries
three displays.  The factorization is already formal, as the corpus's
weighted product identity in `ParityCharacter`; the moment half — the
vanishing of every power moment below the threshold `ω` together with
the exact value of the first survivor — is formal in
`GeneralizedProuhetBlock`.  This module supplies the remaining step,
which that file records as not proved there and which the volume
records as the theorem's only remaining step: the identification of
`ω` with the **order of the zero of the block polynomial at
`z = 1`**.

Write `O_L(a) = {h < L : a h odd}` for the odd layers,
`ω = |O_L(a)|`, and

`T_{a,L}(X) = ∑_{n<2^L} ε_a(n)·X^n ∈ ℤ[X]`

for the block polynomial, `ε_a` being the weighted parity character
of `ParityCharacter`.  The theorem proved here is that `X = 1` is a
root of `T_{a,L}` of multiplicity exactly `ω` — so no root at all
when every layer below `L` is even, which the statement covers.

The mechanism is the factorization
`T_{a,L} = ∏_{h<L} (1 + (-1)^{a_h}·X^{2^h})`, which is the corpus's
weighted product identity read in `ℤ[X]` at `z = X`.  An **odd**
layer contributes `1 - X^{2^h}`, whose geometric cofactor
`∑_{i<2^h} X^i` takes the nonzero value `2^h` at `X = 1`, so that
zero is simple; an **even** layer contributes `1 + X^{2^h}`, which
takes the value `2 ≠ 0` at `X = 1` and so contributes nothing at all.
Multiplicity is additive over products of nonzero polynomials, and
every factor is nonzero because it takes the value `1` at `X = 0`.
Hence the order is exactly the number of odd layers.

Nothing here concerns the analytic canonical product `Φ_a`: this
corpus has no canonical product at general weights, and none is
claimed.  Every statement below is a statement about the polynomial
`T_{a,L}` over `ℤ`.

## Main declarations

* `prouhetFactor` — the layer factor `1 + (-1)^{a_h}·X^{2^h}`;
* `prouhetBlockPoly` — the block polynomial `T_{a,L}`;
* `prouhetBlockPoly_eq_sum` — its coefficient form, definitionally;
* `prouhetBlockPoly_eq_prod` — **its product form**;
* `rootMultiplicity_one_sub_X_pow` — `1 - X^n` has a simple zero at
  `1` whenever `n ≥ 1`;
* `rootMultiplicity_one_add_X_pow` — `1 + X^n` has no zero at `1`;
* `rootMultiplicity_prouhetFactor` — the per-layer multiplicity, `1`
  on an odd layer and `0` on an even one;
* `eval_zero_prouhetFactor` — every factor takes the value `1` at
  `X = 0`;
* `prouhetFactor_ne_zero` and `prod_prouhetFactor_ne_zero` — the
  nonvanishing that multiplicativity of the order needs;
* `rootMultiplicity_prod_prouhetFactor` — **additivity of the order
  over the layer product**;
* `rootMultiplicity_prouhetBlockPoly` — **the headline**: the order
  of the zero of `T_{a,L}` at `1` is `|O_L(a)|`;
* `oddLayers_const_one` — at `a ≡ 1` every layer below `L` is odd;
* `rootMultiplicity_prouhetBlockPoly_const_one` — so the order is
  then exactly `L`;
* `prouhetBlockPoly_const_one` — at `a ≡ 1` the block polynomial is
  the Thue–Morse block;
* `rootMultiplicity_sum_thueMorseSign_mul_X_pow` — **the classical
  statement**: `∑_{n<2^L} ε(n)·X^n` has a zero of order exactly `L`
  at `X = 1`;
* `oddLayers_id_two`, `prouhetBlockPoly_id_two` and
  `rootMultiplicity_prouhetBlockPoly_id_two` — a concrete guard at
  `L = 2` with the weights `a k = k`, where exactly one layer is odd,
  the block polynomial is `1 + X - X² - X³`, and the order is `1` —
  neither `0` nor `2`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The block polynomial and its two forms -/

/-- The `h`-th layer factor of a generalized Prouhet block:
`1 - X^{2^h}` when the weight `a h` is odd and `1 + X^{2^h}` when it
is even. -/
noncomputable def prouhetFactor (a : ℕ → ℕ) (h : ℕ) :
    Polynomial ℤ :=
  1 + Polynomial.C ((-1 : ℤ) ^ a h) * Polynomial.X ^ 2 ^ h

/-- The generalized Prouhet block polynomial
`T_{a,L}(X) = ∑_{n<2^L} ε_a(n)·X^n` over `ℤ`. -/
noncomputable def prouhetBlockPoly (a : ℕ → ℕ) (L : ℕ) :
    Polynomial ℤ :=
  ∑ n ∈ range (2 ^ L),
    Polynomial.C (parityCharacter a n) * Polynomial.X ^ n

/-- The coefficient form of the block polynomial, which is its
definition. -/
theorem prouhetBlockPoly_eq_sum (a : ℕ → ℕ) (L : ℕ) :
    prouhetBlockPoly a L =
      ∑ n ∈ range (2 ^ L),
        Polynomial.C (parityCharacter a n) * Polynomial.X ^ n :=
  rfl

/-- On `ℤ[X]` the integer cast is `Polynomial.C`, because `C` is a
ring homomorphism out of `ℤ`. -/
private theorem intCast_eq_C (m : ℤ) :
    (m : Polynomial ℤ) = Polynomial.C m :=
  (eq_intCast (Polynomial.C : ℤ →+* Polynomial ℤ) m).symm

/-- **The two forms of the block polynomial.**  The coefficient sum
`∑_{n<2^L} ε_a(n)·X^n` is the layer product
`∏_{h<L} (1 + (-1)^{a_h}·X^{2^h})`.  This is the corpus's weighted
product identity `prod_one_add_neg_one_pow_eq_sum_parityCharacter`
instantiated at the commutative ring `ℤ[X]` and the element `X`. -/
theorem prouhetBlockPoly_eq_prod (a : ℕ → ℕ) (L : ℕ) :
    prouhetBlockPoly a L = ∏ h ∈ range L, prouhetFactor a h := by
  have key := prod_one_add_neg_one_pow_eq_sum_parityCharacter a
    (Polynomial.X : Polynomial ℤ) L
  have hsum : ∑ n ∈ range (2 ^ L),
      ((parityCharacter a n : ℤ) : Polynomial ℤ) *
        (Polynomial.X : Polynomial ℤ) ^ n =
      prouhetBlockPoly a L := by
    rw [prouhetBlockPoly_eq_sum]
    simp only [intCast_eq_C]
  have hprod : ∏ j ∈ range L,
      (1 + (((-1 : ℤ) ^ a j : ℤ) : Polynomial ℤ) *
        (Polynomial.X : Polynomial ℤ) ^ 2 ^ j) =
      ∏ h ∈ range L, prouhetFactor a h := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [prouhetFactor]
    simp only [intCast_eq_C]
  rw [← hsum, ← hprod]
  exact key.symm

/-! ## The two per-factor multiplicities -/

/-- A sign depends only on the residue of its exponent modulo two. -/
private theorem neg_one_pow_mod_two' (m : ℕ) :
    (-1 : ℤ) ^ m = (-1) ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The geometric factorization `1 - X^n = -(∑_{i<n} X^i)·(X - 1)`,
written so that the second factor is literally `(X - C 1)^1`. -/
private theorem one_sub_X_pow_eq (n : ℕ) :
    (1 : Polynomial ℤ) - Polynomial.X ^ n =
      (-(∑ i ∈ range n, (Polynomial.X : Polynomial ℤ) ^ i)) *
        (Polynomial.X - Polynomial.C 1) ^ 1 := by
  rw [pow_one, Polynomial.C_1, neg_mul, geom_sum_mul]
  ring

/-- The geometric cofactor takes the value `n` at `X = 1`. -/
private theorem eval_one_geom (n : ℕ) :
    Polynomial.eval (1 : ℤ)
        (∑ i ∈ range n, (Polynomial.X : Polynomial ℤ) ^ i)
      = (n : ℤ) := by
  rw [Polynomial.eval_geom_sum]
  simp

/-- For `n ≥ 1` the geometric cofactor of `1 - X^n` does not vanish
at `X = 1`; this is exactly why the zero there is simple. -/
private theorem eval_one_neg_geom_ne (n : ℕ) (hn : 0 < n) :
    Polynomial.eval (1 : ℤ)
        (-(∑ i ∈ range n, (Polynomial.X : Polynomial ℤ) ^ i))
      ≠ 0 := by
  rw [Polynomial.eval_neg, eval_one_geom]
  simpa using hn.ne'

/-- **A simple zero.**  For `n ≥ 1` the polynomial `1 - X^n`
over `ℤ` has a zero of order exactly one at `X = 1`.  The hypothesis is
essential: at `n = 0` the polynomial is `0`, whose root multiplicity
is `0` by convention. -/
theorem rootMultiplicity_one_sub_X_pow (n : ℕ) (hn : 0 < n) :
    Polynomial.rootMultiplicity (1 : ℤ)
        (1 - Polynomial.X ^ n) = 1 := by
  have hev := eval_one_neg_geom_ne n hn
  have hroot : ¬ Polynomial.IsRoot
      (-(∑ i ∈ range n, (Polynomial.X : Polynomial ℤ) ^ i))
      1 := by
    rw [Polynomial.IsRoot.def]
    exact hev
  have hne : (-(∑ i ∈ range n,
      (Polynomial.X : Polynomial ℤ) ^ i)) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.eval_zero] at hev
    exact hev rfl
  rw [one_sub_X_pow_eq n,
    Polynomial.rootMultiplicity_mul_X_sub_C_pow hne,
    Polynomial.rootMultiplicity_eq_zero hroot, zero_add]

/-- **No zero at all.**  Over `ℤ` the polynomial `1 + X^n` takes the
value `2` at `X = 1`, so its root multiplicity there is `0`.  No
hypothesis on `n` is needed. -/
theorem rootMultiplicity_one_add_X_pow (n : ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ)
        (1 + Polynomial.X ^ n) = 0 := by
  refine Polynomial.rootMultiplicity_eq_zero ?_
  rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow]
  norm_num

/-- **The per-layer multiplicity.**  An odd layer contributes a simple
zero at `X = 1`; an even layer contributes nothing. -/
theorem rootMultiplicity_prouhetFactor (a : ℕ → ℕ) (h : ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ) (prouhetFactor a h) =
      if a h % 2 = 1 then 1 else 0 := by
  by_cases hodd : a h % 2 = 1
  · have hsign : ((-1 : ℤ) ^ a h) = -1 := by
      rw [neg_one_pow_mod_two' (a h), hodd, pow_one]
    have hfac : prouhetFactor a h =
        1 - (Polynomial.X : Polynomial ℤ) ^ 2 ^ h := by
      rw [prouhetFactor, hsign, Polynomial.C_neg, Polynomial.C_1]
      ring
    rw [hfac, if_pos hodd,
      rootMultiplicity_one_sub_X_pow (2 ^ h) (Nat.two_pow_pos h)]
  · have heven : a h % 2 = 0 := by omega
    have hsign : ((-1 : ℤ) ^ a h) = 1 := by
      rw [neg_one_pow_mod_two' (a h), heven, pow_zero]
    have hfac : prouhetFactor a h =
        1 + (Polynomial.X : Polynomial ℤ) ^ 2 ^ h := by
      rw [prouhetFactor, hsign, Polynomial.C_1, one_mul]
    rw [hfac, if_neg hodd, rootMultiplicity_one_add_X_pow]

/-! ## Nonvanishing, and additivity over the layer product -/

/-- Every layer factor takes the value `1` at `X = 0`, because the
exponent `2^h` is positive. -/
theorem eval_zero_prouhetFactor (a : ℕ → ℕ) (h : ℕ) :
    Polynomial.eval (0 : ℤ) (prouhetFactor a h) = 1 := by
  rw [prouhetFactor, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, zero_pow (Nat.two_pow_pos h).ne', mul_zero,
    add_zero]

/-- No layer factor is the zero polynomial. -/
theorem prouhetFactor_ne_zero (a : ℕ → ℕ) (h : ℕ) :
    prouhetFactor a h ≠ 0 := by
  intro h0
  have hev := eval_zero_prouhetFactor a h
  rw [h0, Polynomial.eval_zero] at hev
  exact zero_ne_one hev

/-- **The layer product never vanishes**, over any set of layers: it
too takes the value `1` at `X = 0`.  This is the hypothesis that
`Polynomial.rootMultiplicity_mul` requires. -/
theorem prod_prouhetFactor_ne_zero (a : ℕ → ℕ) (s : Finset ℕ) :
    (∏ h ∈ s, prouhetFactor a h) ≠ 0 := by
  intro h0
  have hev : Polynomial.eval (0 : ℤ)
      (∏ h ∈ s, prouhetFactor a h) = 1 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_one fun h _ => eval_zero_prouhetFactor a h
  rw [h0, Polynomial.eval_zero] at hev
  exact zero_ne_one hev

/-- The root multiplicity of the constant polynomial `1`. -/
private theorem rootMultiplicity_one_one :
    Polynomial.rootMultiplicity (1 : ℤ) 1 = 0 := by
  have h := Polynomial.rootMultiplicity_C (1 : ℤ) (1 : ℤ)
  rwa [Polynomial.C_1] at h

/-- **Additivity of the order over the layer product.**  Root
multiplicity is additive on products of nonzero polynomials, and each
partial layer product is nonzero, so the order of the zero of a layer
product at `1` is the sum of the per-layer orders. -/
theorem rootMultiplicity_prod_prouhetFactor (a : ℕ → ℕ)
    (s : Finset ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ)
        (∏ h ∈ s, prouhetFactor a h) =
      ∑ h ∈ s,
        Polynomial.rootMultiplicity (1 : ℤ) (prouhetFactor a h) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact rootMultiplicity_one_one
  | insert b s hb ih =>
      have hne : prouhetFactor a b * (∏ h ∈ s, prouhetFactor a h)
          ≠ 0 := by
        have h1 := prod_prouhetFactor_ne_zero a (insert b s)
        rwa [Finset.prod_insert hb] at h1
      rw [Finset.prod_insert hb, Polynomial.rootMultiplicity_mul hne,
        ih, Finset.sum_insert hb]

/-! ## The order of the zero at `z = 1` -/

/-- The number of odd layers, counted as a sum of indicators. -/
private theorem card_oddLayers_eq_sum (a : ℕ → ℕ) (L : ℕ) :
    (oddLayers a L).card =
      ∑ h ∈ range L, if a h % 2 = 1 then 1 else 0 := by
  rw [oddLayers]
  exact Finset.card_filter _ _

/-- **The order of the zero of a generalized Prouhet block at
`z = 1`.**  With `O_L(a) = {h < L : a h odd}`, the block polynomial
`T_{a,L}(X) = ∑_{n<2^L} ε_a(n)·X^n` has at `X = 1` a zero of order
exactly `|O_L(a)|`, and so no zero at all when every layer below `L`
is even — the same `ω` that indexes the first surviving
power moment in `sum_range_two_pow_parityCharacter_mul_pow`.  This
closes the last open step of the volume's generalized Prouhet
theorem. -/
theorem rootMultiplicity_prouhetBlockPoly (a : ℕ → ℕ) (L : ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ) (prouhetBlockPoly a L) =
      (oddLayers a L).card := by
  rw [prouhetBlockPoly_eq_prod, rootMultiplicity_prod_prouhetFactor,
    card_oddLayers_eq_sum]
  exact Finset.sum_congr rfl fun h _ =>
    rootMultiplicity_prouhetFactor a h

/-! ## The constant-weight reading -/

/-- At the constant weight `a ≡ 1` every layer below `L` is odd. -/
theorem oddLayers_const_one (L : ℕ) :
    oddLayers (fun _ => 1) L = range L := by
  ext h
  simp [oddLayers]

/-- **Constant weights: the order is exactly `L`.** -/
theorem rootMultiplicity_prouhetBlockPoly_const_one (L : ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ)
        (prouhetBlockPoly (fun _ => 1) L) = L := by
  rw [rootMultiplicity_prouhetBlockPoly, oddLayers_const_one,
    Finset.card_range]

/-- At `a ≡ 1` the weighted character is the Thue–Morse sign, so the
block polynomial is the length-`2^L` Thue–Morse block. -/
theorem prouhetBlockPoly_const_one (L : ℕ) :
    prouhetBlockPoly (fun _ => 1) L =
      ∑ n ∈ range (2 ^ L),
        Polynomial.C (thueMorseSign n) * Polynomial.X ^ n := by
  rw [prouhetBlockPoly_eq_sum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [parityCharacter_const_one]

/-- **The classical statement.**  The length-`2^L` Thue–Morse block
polynomial `∑_{n<2^L} ε(n)·X^n` has at `X = 1` a zero of order
exactly `L`.

The corpus already carries this polynomial in monomial form as
`Fabius.thueMorseBlockPolynomial` (`ThueMorseGenerating`); the two
spellings agree by `Polynomial.C_mul_X_pow_eq_monomial`, but that
module is not imported here, so the sum is written out. -/
theorem rootMultiplicity_sum_thueMorseSign_mul_X_pow (L : ℕ) :
    Polynomial.rootMultiplicity (1 : ℤ)
        (∑ n ∈ range (2 ^ L),
          Polynomial.C (thueMorseSign n) * Polynomial.X ^ n) = L := by
  rw [← prouhetBlockPoly_const_one,
    rootMultiplicity_prouhetBlockPoly_const_one]

/-! ## A concrete guard -/

/-- With the weights `a k = k`, layer `0` is even and layer `1` is
odd, so exactly one layer below `2` is odd. -/
theorem oddLayers_id_two : oddLayers (fun k => k) 2 = {1} := by
  ext h
  simp only [mem_oddLayers, Finset.mem_range, Finset.mem_singleton]
  omega

/-- With the weights `a k = k` and `L = 2` the block polynomial is
`(1 + X)·(1 - X²) = 1 + X - X² - X³`: the even layer `0` contributes
`1 + X` and the odd layer `1` contributes `1 - X²`.

This is derived through the product form, so it checks the factor
bookkeeping rather than independently certifying the coefficient
form. -/
theorem prouhetBlockPoly_id_two :
    prouhetBlockPoly (fun k => k) 2 =
      1 + Polynomial.X - Polynomial.X ^ 2 - Polynomial.X ^ 3 := by
  have h0 : prouhetFactor (fun k => k) 0 =
      1 + (Polynomial.X : Polynomial ℤ) := by
    have hs : ((-1 : ℤ) ^ (0 : ℕ)) = 1 := pow_zero (-1)
    have hp : (2 : ℕ) ^ (0 : ℕ) = 1 := pow_zero 2
    show (1 : Polynomial ℤ) +
        Polynomial.C ((-1 : ℤ) ^ (0 : ℕ)) *
          (Polynomial.X : Polynomial ℤ) ^ 2 ^ (0 : ℕ) =
      1 + Polynomial.X
    rw [hs, hp, Polynomial.C_1, one_mul, pow_one]
  have h1 : prouhetFactor (fun k => k) 1 =
      1 - (Polynomial.X : Polynomial ℤ) ^ 2 := by
    have hs : ((-1 : ℤ) ^ (1 : ℕ)) = -1 := pow_one (-1)
    have hp : (2 : ℕ) ^ (1 : ℕ) = 2 := pow_one 2
    show (1 : Polynomial ℤ) +
        Polynomial.C ((-1 : ℤ) ^ (1 : ℕ)) *
          (Polynomial.X : Polynomial ℤ) ^ 2 ^ (1 : ℕ) =
      1 - Polynomial.X ^ 2
    rw [hs, hp, Polynomial.C_neg, Polynomial.C_1]
    ring
  have hr : (∏ h ∈ range 2, prouhetFactor (fun k => k) h) =
      ∏ h ∈ range (1 + 1), prouhetFactor (fun k => k) h := rfl
  have hp2 : (∏ h ∈ range 2, prouhetFactor (fun k => k) h) =
      prouhetFactor (fun k => k) 0 *
        prouhetFactor (fun k => k) 1 := by
    rw [hr, Finset.prod_range_succ, Finset.prod_range_one]
  rw [prouhetBlockPoly_eq_prod, hp2, h0, h1]
  ring

/-- **The guard.**  At `L = 2` with the weights `a k = k` the order of
the zero at `X = 1` is `1` — neither `0`, which an even layer would
give, nor `2`, which counting all layers rather than the odd ones
would give. -/
theorem rootMultiplicity_prouhetBlockPoly_id_two :
    Polynomial.rootMultiplicity (1 : ℤ)
        (prouhetBlockPoly (fun k => k) 2) = 1 := by
  rw [rootMultiplicity_prouhetBlockPoly, oddLayers_id_two,
    Finset.card_singleton]

end Fabius
