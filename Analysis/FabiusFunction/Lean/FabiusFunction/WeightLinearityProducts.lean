import FabiusFunction.GeneralizedRvachevProduct

/-!
# From exponent identities to product identities

`GeneralizedRvachevProduct` proves that `a ↦ Φ_a` turns a *sum* of two
admissible weights into a *product*
(`generalizedRvachevProduct_add`).  The exponents volume needs the
consequence of that repeatedly, and named the gap exactly: of the
finite-difference factorization it said the exponent-level content was
formal, so that "what is missing is exactly the passage from the
exponent identity to the product identity, not the combinatorics".
The docstring of `generalizedRvachevProduct_two_mul` recorded the same
thing.  (Both have since been updated to point here, so neither now
reads as written above.)

This module supplies the passage once and in general.  If a weight is
any `ℕ`-linear combination of admissible weights,

`a h = ∑_{i ∈ s} c i · w i h`  for every `h`,

then

`Φ_a(z) = ∏_{i ∈ s} Φ_{w i}(z) ^ (c i)`

at every `z`, with no hypothesis beyond admissibility of the pieces
(`generalizedRvachevProduct_linearCombination`).  The index set is an
arbitrary `Finset`, so this covers every such identity at once: the
volume's finite-difference factorization is the instance
`s = range (m+1)`, `c r = C(m,r)`.

Two remarks on what is and is not claimed.

The coefficients are **natural numbers**.  That is not a convenience
but the boundary of the statement: `Φ_a` is defined only for `a`
valued in `ℕ`, so a combination with a negative coefficient does not
name a transform at all.  The volume is aware of this — it calls the
finite-difference identity "initially an identity of analytic germs;
all apparent poles cancel whenever the left side is entire".  Here the
identity is proved where both sides are literally defined, and the
germ-level statement for signed differences is not addressed.

The shift is included because it is the volume's own application:
`shiftExponent_iterate` identifies `S^m a` as `h ↦ a (h + m)`, and
`generalizedRvachevProduct_shift_factorization` is the factorization
of `Φ_{S^m a}` for any presentation of the shifted weight as a
nonnegative binomial combination.

* `Fabius.summable_weight_natMul`, `Fabius.summable_weight_add`,
  `Fabius.summable_weight_linearCombination` — admissibility is
  closed under `ℕ`-linear combination;
* `Fabius.generalizedRvachevProduct_natMul` — `Φ_{k·a} = (Φ_a)^k`;
* `Fabius.generalizedRvachevProduct_linearCombination` — **the
  passage**;
* `Fabius.shiftExponent_iterate`,
  `Fabius.summable_shiftExponent_iterate` — the iterated shift;
* `Fabius.generalizedRvachevProduct_shift_factorization` — the
  volume's finite-difference factorization, where its differences are
  nonnegative.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Admissibility is closed under `ℕ`-linear combination -/

/-- Scaling a weight by `k : ℕ` preserves admissibility. -/
theorem summable_weight_natMul (k : ℕ) (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) :
    Summable fun h : ℕ => ((k * a h : ℕ) : ℝ) / 2 ^ h := by
  refine (ha.mul_left (k : ℝ)).congr fun h => ?_
  push_cast
  ring

/-- Adding two weights preserves admissibility. -/
theorem summable_weight_add (a b : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (hb : Summable fun h : ℕ => (b h : ℝ) / 2 ^ h) :
    Summable fun h : ℕ => ((a h + b h : ℕ) : ℝ) / 2 ^ h := by
  refine (ha.add hb).congr fun h => ?_
  push_cast
  ring

/-- A `ℕ`-linear combination of admissible weights is admissible. -/
theorem summable_weight_linearCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℕ) (w : ι → ℕ → ℕ)
    (hw : ∀ i ∈ s, Summable fun h : ℕ => (w i h : ℝ) / 2 ^ h) :
    Summable fun h : ℕ =>
      ((∑ i ∈ s, c i * w i h : ℕ) : ℝ) / 2 ^ h := by
  induction s using Finset.cons_induction with
  | empty => simpa using summable_zero
  | cons i s hi IH =>
    have hi' := hw i (Finset.mem_cons_self i s)
    have hrest : ∀ j ∈ s,
        Summable fun h : ℕ => (w j h : ℝ) / 2 ^ h := fun j hj =>
      hw j (Finset.mem_cons_of_mem hj)
    have hsum := summable_weight_add (fun h => c i * w i h)
      (fun h => ∑ j ∈ s, c j * w j h)
      (summable_weight_natMul (c i) (w i) hi') (IH hrest)
    refine hsum.congr fun h => ?_
    rw [Finset.sum_cons]

/-! ## The transform on a scaled weight -/

/-- **`Φ` on a scaled weight**: `Φ_{k·a} = (Φ_a)^k`.

Induction on `k` from `generalizedRvachevProduct_add`, since
`(k+1)·a = k·a + a`. -/
theorem generalizedRvachevProduct_natMul (k : ℕ) (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) :
    generalizedRvachevProduct (fun h => k * a h) z
      = generalizedRvachevProduct a z ^ k := by
  induction k with
  | zero =>
    have hz : (fun h : ℕ => 0 * a h) = fun _ : ℕ => 0 := by
      funext h
      exact Nat.zero_mul _
    rw [hz, generalizedRvachevProduct_zero_exponent, pow_zero]
  | succ k IH =>
    have hstep : (fun h : ℕ => (k + 1) * a h)
        = (fun h : ℕ => k * a h) + a := by
      funext h
      show (k + 1) * a h = k * a h + a h
      ring
    rw [hstep, generalizedRvachevProduct_add _ _
      (summable_weight_natMul k a ha) ha, IH, pow_succ]

/-! ## The passage -/

/-- **Every `ℕ`-linear identity among admissible weights is an
identity of products.**  If

`a h = ∑_{i ∈ s} c i · w i h`  for every `h`,

then `Φ_a(z) = ∏_{i ∈ s} Φ_{w i}(z) ^ (c i)`.

This is the step the exponents volume identifies as the one thing
missing between its exponent combinatorics and its product identities.
Nothing about the particular combination is used: the proof is
induction over `s` on `generalizedRvachevProduct_add` and
`generalizedRvachevProduct_natMul`. -/
theorem generalizedRvachevProduct_linearCombination {ι : Type*}
    (s : Finset ι) (a : ℕ → ℕ) (c : ι → ℕ) (w : ι → ℕ → ℕ)
    (hw : ∀ i ∈ s, Summable fun h : ℕ => (w i h : ℝ) / 2 ^ h)
    (hEq : ∀ h : ℕ, a h = ∑ i ∈ s, c i * w i h) (z : ℂ) :
    generalizedRvachevProduct a z
      = ∏ i ∈ s, generalizedRvachevProduct (w i) z ^ c i := by
  induction s using Finset.cons_induction generalizing a with
  | empty =>
    have hz : a = fun _ : ℕ => 0 := by
      funext h
      simpa using hEq h
    rw [hz, generalizedRvachevProduct_zero_exponent,
      Finset.prod_empty]
  | cons i s hi IH =>
    have hi' := hw i (Finset.mem_cons_self i s)
    have hrest : ∀ j ∈ s,
        Summable fun h : ℕ => (w j h : ℝ) / 2 ^ h := fun j hj =>
      hw j (Finset.mem_cons_of_mem hj)
    have hsplit : a = (fun h : ℕ => c i * w i h)
        + fun h : ℕ => ∑ j ∈ s, c j * w j h := by
      funext h
      show a h = c i * w i h + ∑ j ∈ s, c j * w j h
      rw [hEq h, Finset.sum_cons]
    rw [hsplit, generalizedRvachevProduct_add _ _
      (summable_weight_natMul (c i) (w i) hi')
      (summable_weight_linearCombination s c w hrest),
      generalizedRvachevProduct_natMul (c i) (w i) hi',
      IH (fun h : ℕ => ∑ j ∈ s, c j * w j h) hrest (fun _ => rfl),
      Finset.prod_cons]

/-! ## The iterated shift -/

/-- The `m`-fold shift deletes the first `m` layers:
`S^m a = fun h => a (h + m)`. -/
theorem shiftExponent_iterate (a : ℕ → ℕ) (m : ℕ) :
    shiftExponent^[m] a = fun h : ℕ => a (h + m) := by
  induction m generalizing a with
  | zero => simp
  | succ m IH =>
    rw [Function.iterate_succ_apply, IH (shiftExponent a)]
    funext h
    show a (h + m + 1) = a (h + (m + 1))
    rw [Nat.add_assoc]

/-- Admissibility survives any number of shifts. -/
theorem summable_shiftExponent_iterate (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ) :
    Summable fun h : ℕ => ((shiftExponent^[m] a) h : ℝ) / 2 ^ h := by
  induction m with
  | zero => simpa using ha
  | succ m IH =>
    rw [Function.iterate_succ_apply']
    exact summable_shiftExponent _ IH

/-- **The finite-difference factorization**, wherever the differences
it uses are nonnegative.

The volume writes `Φ_{S^m a} = ∏_{r ≤ m} Φ_{Δ^r a} ^ C(m,r)` and
observes that it is "initially an identity of analytic germs" because
`Δ^r a` may be negative.  Presented with any family `D` of *natural*
weights realising the Gregory–Newton expansion of the shifted weight,

`a (h + m) = ∑_{r ≤ m} C(m,r) · D r h`,

the identity is an honest identity of products, with both sides
defined.  `D r = Δ^r a` is the intended reading, and the hypothesis is
then exactly the statement that those differences are nonnegative --
the case in which the volume's display needs no germ. -/
theorem generalizedRvachevProduct_shift_factorization (a : ℕ → ℕ)
    (m : ℕ) (D : ℕ → ℕ → ℕ)
    (hD : ∀ r ∈ range (m + 1),
      Summable fun h : ℕ => (D r h : ℝ) / 2 ^ h)
    (hNewton : ∀ h : ℕ,
      a (h + m) = ∑ r ∈ range (m + 1), m.choose r * D r h)
    (z : ℂ) :
    generalizedRvachevProduct (shiftExponent^[m] a) z
      = ∏ r ∈ range (m + 1),
          generalizedRvachevProduct (D r) z ^ m.choose r := by
  refine generalizedRvachevProduct_linearCombination (range (m + 1))
    _ (fun r => m.choose r) D hD (fun h => ?_) z
  rw [shiftExponent_iterate]
  exact hNewton h

end Fabius
