import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Intervals
import FabiusFunction.QPochhammerDissection

/-!
# The Borwein dissection: reciprocity and two-ended stabilization

The Borwein product is

`P_n(q) = (q;q)_{3n} / (q^3;q^3)_n = ∏_{j=1}^{n} (1 - q^{3j-2})(1 - q^{3j-1})`,

a polynomial of degree `3n^2`.  Sorting its monomials by the residue of the
exponent modulo `3` produces three polynomials `A_n, B_n, C_n` with

`P_n(q) = A_n(q^3) - q B_n(q^3) - q^2 C_n(q^3)`.

The minus signs are part of the normalization; **nothing in this file assumes
or asserts a sign for any coefficient**.

Two facts are proved here.

*Reciprocity.*  `P_n` is palindromic in degree `3n^2`, because each `j`-block
contributes two factors `1 - q^a`, and `(1 - q^{-a})(1 - q^{-b})
= q^{-a-b}(1 - q^a)(1 - q^b)`: the two sign flips cancel.  Splitting the
palindromy by residue classes modulo `3` gives

`A_n(x) = x^{n^2} A_n(1/x)`, `B_n(x) = x^{n^2-1} C_n(1/x)`,
`C_n(x) = x^{n^2-1} B_n(1/x)`,

and hence `B_n(1) = C_n(1)` and `A_n(1) = 2 B_n(1)` for `n ≥ 1`.

*Two-ended stabilization.*  Deleting the blocks with index `> N` changes `P_n`
only in degrees `≥ 3N + 1`, so `X^{3N+1} ∣ P_n - P_N` whenever `N ≤ n`.  With
`N = d + 1` this pins the three coefficients in degrees `3d`, `3d+1`, `3d+2`,
that is `a_{n,d}`, `b_{n,d}`, `c_{n,d}`; reciprocity then transports them to
the opposite end.

## Generality

Everything is stated over an **arbitrary commutative ring** `R`, not just over
`ℤ[x]` as in the printed source: `Polynomial.reflect`, divisibility by `X^m`,
`Polynomial.expand`/`Polynomial.contract` and every `ring` identity used below
are characteristic-free and domain-free.  The monograph's case is `R = ℤ`.

Three further deliberate choices, all strengthenings or normalizations of the
print rather than corrections of it:

* the blocks are indexed by `j ∈ Finset.range n` as
  `(1 - X^{3j+1})(1 - X^{3j+2})` rather than by `j = 1, …, n` as
  `(1 - q^{3j-2})(1 - q^{3j-1})`.  This is literally the same product under
  `j ↦ j + 1` and it removes truncated `ℕ` subtraction from every index;
* the `q`-adic stabilization is proved in the general form
  `X^{3N+1} ∣ P_n - P_N` for all `N ≤ n` (`X_pow_dvd_borweinProduct_sub`), not
  only in the instance `N = d + 1` consumed by the tail-stabilization
  statement;
* reciprocity in coefficient form is stated with the subtraction-free
  hypotheses `r + s = n^2` and `r + s + 1 = n^2` instead of an index `n^2 - r`.
  In `ℕ` this is not cosmetic: it makes the reflected index total, keeps every
  downstream `omega` goal first-order, and encodes the range condition in the
  hypothesis.  (The printed proof quantifies the three reflected-index
  identities over "every `n`"; with the usual convention that a coefficient
  outside the degree range is `0`, and with `n ≥ d + 1` supplied by the
  enclosing proposition, the printed argument is correct as written.  Nothing
  in the source is being corrected here.)

## Main declarations

* `borweinBlock`, `borweinProduct`: the `j`-th block and `P_n`.
* `borweinA`, `borweinB`, `borweinC`: the three residue components, with
  `coeff_borweinA`, `coeff_borweinB`, `coeff_borweinC` reading off
  `a_{n,r} = [q^{3r}]P_n`, `b_{n,r} = -[q^{3r+1}]P_n`,
  `c_{n,r} = -[q^{3r+2}]P_n`.
* `borweinProduct_dissection`: the defining trisection
  `P_n = A_n(X^3) - X·B_n(X^3) - X^2·C_n(X^3)` — proved, not assumed.
* `reflect_borweinProduct`, `coeff_borweinProduct_rev`: palindromy of `P_n`.
* `coeff_borweinA_rev`, `coeff_borweinB_rev`, `coeff_borweinC_rev` and
  `reflect_borweinA`, `reflect_borweinB`, `reflect_borweinC`: reciprocity, in
  coefficient form and in polynomial form.  Note `Polynomial.reflect N f` *is*
  `x^N f(1/x)` when `f.natDegree ≤ N`, so the three `reflect_*` statements are
  exactly the three printed identities (with `reflect_borweinB` carrying the
  print's *third* identity `C_n(x) = x^{n^2-1}B_n(1/x)` and
  `reflect_borweinC` its *second* one — reflection reads them in the opposite
  direction).
* `eval_one_borweinB_eq_borweinC`, `eval_one_borweinA`: the two "in particular"
  corollaries `B_n(1) = C_n(1)` and `A_n(1) = 2 B_n(1)`, for `n ≥ 1`.
* `X_pow_dvd_borweinProduct_sub`, `coeff_borweinProduct_stable`: `q`-adic
  stabilization of the finite product.
* `coeff_borweinA_stabilize`, `coeff_borweinB_stabilize`,
  `coeff_borweinC_stabilize` (lower end) and `coeff_borweinA_top`,
  `coeff_borweinB_top`, `coeff_borweinC_top` (upper end): the six identities of
  the two-ended stabilization proposition.
* `finiteQPochhammerIn_three_mul`, `finiteQPochhammerIn_three_mul_X`: the
  division-free form of the quotient definition
  `P_n(q) = (q;q)_{3n}/(q^3;q^3)_n`, over an arbitrary commutative ring and an
  arbitrary ring element `q`.

## What is NOT covered

* **No positivity.**  No statement about the signs of the coefficients of
  `A_n, B_n, C_n` is made, proved or used.  The Borwein conjecture (settled
  externally by Wang and by Wang–Krattenthaler) is not reproduced here; the
  printed propositions are themselves sign-free, and the source's own
  historical paragraph says the same.
* **No general truncation principle.**  The monograph's general truncation
  principle (arbitrary integer exponent sequences, coefficientwise limits in
  `ℤ[[q]]`) is not formalized.  Only the finite-product `q`-adic stabilization
  actually needed is proved, and only for the Borwein product, inside `R[X]`
  rather than `R[[q]]`.  That is strictly enough for the tail-stabilization
  proposition.
* **No filter repackaging.**  "Every fixed-distance coefficient is eventually
  constant" is not phrased with `Filter.EventuallyEq`; the explicit equalities
  given here are stronger and effective.
* **No uniqueness.**  Existence of a triple `(A_n, B_n, C_n)` satisfying
  `borweinProduct_dissection` is proved; uniqueness is not.
* **No exact degrees.**  Only the upper bounds `natDegree_borweinA_le` etc. are
  proved; that `A_n` really has degree `n^2` (which needs `R` nontrivial) is
  neither stated nor needed.
-/

set_option autoImplicit false

open scoped BigOperators

open Polynomial

namespace Fabius

/-! ### Generic helpers about `Polynomial.reflect`

These three lemmas hold over an arbitrary (commutative) semiring.  They carry
fresh names so as not to collide with the similar helpers in
`GaussianBinomialPalindromic`. -/

/-- Reflecting the constant polynomial `1` in degree `N` gives `X ^ N`.  This is
`Polynomial.reflect_one` restated with the reflection degree explicit; it is kept as a
named corpus lemma because the `rw`-chains below quote it by this name. -/
theorem reflect_one_eq_X_pow {S : Type*} [Semiring S] (N : ℕ) :
    reflect N (1 : S[X]) = X ^ N :=
  Polynomial.reflect_one N

/-- A polynomial of degree at most `N` reflects in degree `N` onto `g` as soon as its
coefficient sequence read backwards is that of `g`.  This is the workhorse turning a
coefficient identity into the polynomial identity `x^N f(1/x) = g(x)`. -/
theorem reflect_eq_of_coeff_rev {S : Type*} [Semiring S] {N : ℕ} {f g : S[X]}
    (hf : f.natDegree ≤ N) (hg : g.natDegree ≤ N)
    (h : ∀ i, i ≤ N → f.coeff (N - i) = g.coeff i) :
    reflect N f = g := by
  ext i
  rw [coeff_reflect]
  rcases le_or_gt i N with hi | hi
  · rw [revAt_le hi]
    exact h i hi
  · rw [revAt_eq_self_of_lt hi, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hi),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg hi)]

/-- Reflection does not change the value at `1`: reversing a finite coefficient sequence
does not change its sum. -/
theorem eval_one_reflect {S : Type*} [CommSemiring S] {N : ℕ} {f : S[X]}
    (hf : f.natDegree ≤ N) :
    (reflect N f).eval 1 = f.eval 1 := by
  have hle : (reflect N f).natDegree ≤ N := natDegree_reflect_le.trans (max_le le_rfl hf)
  have hrd : (reflect N f).natDegree < N + 1 := by omega
  have hfd : f.natDegree < N + 1 := by omega
  rw [eval_eq_sum_range' hrd, eval_eq_sum_range' hfd]
  simp only [one_pow, mul_one, coeff_reflect]
  rw [← Finset.sum_range_reflect (fun j => f.coeff j) (N + 1)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjmem : j < N + 1 := Finset.mem_range.mp hj
  have hjN : j ≤ N := by omega
  rw [revAt_le hjN]
  exact congrArg (fun i => f.coeff i) (by omega)

/-! ### The Borwein product -/

/-- The `j`-th block `(1 - X^{3j+1})(1 - X^{3j+2})` of the Borwein product.

The printed source indexes the blocks by `j = 1, …, n` as
`(1 - q^{3j-2})(1 - q^{3j-1})`; the shift `j ↦ j + 1` used here gives literally the same
product while keeping every exponent free of truncated `ℕ` subtraction. -/
noncomputable def borweinBlock (R : Type*) [CommRing R] (j : ℕ) : R[X] :=
  (1 - X ^ (3 * j + 1)) * (1 - X ^ (3 * j + 2))

/-- Unfolding lemma for `borweinBlock`. -/
theorem borweinBlock_def (R : Type*) [CommRing R] (j : ℕ) :
    borweinBlock R j = (1 - X ^ (3 * j + 1)) * (1 - X ^ (3 * j + 2)) := rfl

/-- The Borwein product `P_n(X) = ∏_{j<n} (1 - X^{3j+1})(1 - X^{3j+2})`, of degree `3n^2`. -/
noncomputable def borweinProduct (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.range n, borweinBlock R j

/-- Unfolding lemma for `borweinProduct`. -/
theorem borweinProduct_def (R : Type*) [CommRing R] (n : ℕ) :
    borweinProduct R n = ∏ j ∈ Finset.range n, borweinBlock R j := rfl

/-- The empty Borwein product is `1`. -/
theorem borweinProduct_zero (R : Type*) [CommRing R] : borweinProduct R 0 = 1 :=
  Finset.prod_range_zero (borweinBlock R)

/-- Peeling the last block. -/
theorem borweinProduct_succ (R : Type*) [CommRing R] (n : ℕ) :
    borweinProduct R (n + 1) = borweinProduct R n * borweinBlock R n :=
  Finset.prod_range_succ (borweinBlock R) n

/-- Each block has degree at most `6j + 3 = (3j+1) + (3j+2)`. -/
theorem natDegree_borweinBlock_le (R : Type*) [CommRing R] (j : ℕ) :
    (borweinBlock R j).natDegree ≤ 6 * j + 3 := by
  have h₁ : ((1 : R[X]) - X ^ (3 * j + 1)).natDegree ≤ 3 * j + 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le _))
  have h₂ : ((1 : R[X]) - X ^ (3 * j + 2)).natDegree ≤ 3 * j + 2 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le _))
  have h : (borweinBlock R j).natDegree ≤ 3 * j + 1 + (3 * j + 2) := by
    rw [borweinBlock_def]
    exact natDegree_mul_le.trans (Nat.add_le_add h₁ h₂)
  omega

/-- `P_n` has degree at most `3n^2`; this is the printed degree count
`∑_{j=1}^n ((3j-2) + (3j-1)) = 3n^2`. -/
theorem natDegree_borweinProduct_le (R : Type*) [CommRing R] (n : ℕ) :
    (borweinProduct R n).natDegree ≤ 3 * n ^ 2 := by
  induction n with
  | zero =>
      show (borweinProduct R 0).natDegree ≤ 3 * 0 ^ 2
      rw [borweinProduct_zero]
      simp
  | succ n ih =>
      show (borweinProduct R (n + 1)).natDegree ≤ 3 * (n + 1) ^ 2
      rw [borweinProduct_succ]
      calc (borweinProduct R n * borweinBlock R n).natDegree
          ≤ (borweinProduct R n).natDegree + (borweinBlock R n).natDegree := natDegree_mul_le
        _ ≤ 3 * n ^ 2 + (6 * n + 3) := Nat.add_le_add ih (natDegree_borweinBlock_le R n)
        _ = 3 * (n + 1) ^ 2 := by ring

/-! ### Palindromy of the Borwein product -/

/-- Each block is palindromic in degree `6j + 3`.  This is the Lean form of the printed
observation that a `j`-block carries **two** factors `1 - q^a`, so the two sign flips in
`1 - q^{-a} = -q^{-a}(1 - q^a)` cancel. -/
theorem reflect_borweinBlock (R : Type*) [CommRing R] (j : ℕ) :
    reflect (6 * j + 3) (borweinBlock R j) = borweinBlock R j := by
  have hd₁ : ((1 : R[X]) - X ^ (3 * j + 1)).natDegree ≤ 3 * j + 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le _))
  have hd₂ : ((1 : R[X]) - X ^ (3 * j + 2)).natDegree ≤ 3 * j + 2 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_X_pow_le _))
  have hsum : 6 * j + 3 = 3 * j + 1 + (3 * j + 2) := by ring
  have key : ∀ m : ℕ, reflect m ((1 : R[X]) - X ^ m) = -(1 - X ^ m) := by
    intro m
    rw [reflect_sub, reflect_one_eq_X_pow, reflect_monomial, revAt_le (le_refl m), Nat.sub_self,
      pow_zero, neg_sub]
  rw [borweinBlock_def, hsum, reflect_mul _ _ hd₁ hd₂, key, key, neg_mul_neg]

/-- **`P_n` is palindromic in degree `3n^2`**, i.e. `P_n(q) = q^{3n^2} P_n(1/q)`. -/
theorem reflect_borweinProduct (R : Type*) [CommRing R] (n : ℕ) :
    reflect (3 * n ^ 2) (borweinProduct R n) = borweinProduct R n := by
  induction n with
  | zero =>
      show reflect (3 * 0 ^ 2) (borweinProduct R 0) = borweinProduct R 0
      rw [borweinProduct_zero]
      simp
  | succ n ih =>
      show reflect (3 * (n + 1) ^ 2) (borweinProduct R (n + 1)) = borweinProduct R (n + 1)
      have hsum : 3 * (n + 1) ^ 2 = 3 * n ^ 2 + (6 * n + 3) := by ring
      rw [borweinProduct_succ, hsum,
        reflect_mul _ _ (natDegree_borweinProduct_le R n) (natDegree_borweinBlock_le R n), ih,
        reflect_borweinBlock]

/-- The coefficient form of the palindromy, in subtraction-free indexing:
`[q^r]P_n = [q^s]P_n` whenever `r + s = 3n^2`. -/
theorem coeff_borweinProduct_rev (R : Type*) [CommRing R] {n r s : ℕ} (h : r + s = 3 * n ^ 2) :
    (borweinProduct R n).coeff r = (borweinProduct R n).coeff s := by
  have hs : s ≤ 3 * n ^ 2 := by omega
  have hrs : 3 * n ^ 2 - s = r := by omega
  conv_rhs => rw [← reflect_borweinProduct R n]
  rw [coeff_reflect, revAt_le hs, hrs]

/-! ### `q`-adic stabilization of the finite product -/

/-- The block `(1 - X^{3(N+k)+1})(1 - X^{3(N+k)+2})` is congruent to `1` modulo `X^{3N+1}`,
because both of its nonconstant exponents are at least `3N + 1`. -/
theorem X_pow_dvd_borweinBlock_sub_one (R : Type*) [CommRing R] (N k : ℕ) :
    (X : R[X]) ^ (3 * N + 1) ∣ borweinBlock R (N + k) - 1 := by
  refine ⟨X ^ (3 * N + 1) * X ^ (3 * k) * X ^ (3 * k + 1) - X ^ (3 * k) - X ^ (3 * k + 1), ?_⟩
  rw [borweinBlock_def]
  ring

/-- `q`-adic stabilization of the Borwein product in additive index form:
`X^{3N+1} ∣ P_{N+k} - P_N`. -/
theorem X_pow_dvd_borweinProduct_sub_aux (R : Type*) [CommRing R] (N k : ℕ) :
    (X : R[X]) ^ (3 * N + 1) ∣ borweinProduct R (N + k) - borweinProduct R N := by
  induction k with
  | zero =>
      show (X : R[X]) ^ (3 * N + 1) ∣ borweinProduct R (N + 0) - borweinProduct R N
      simp
  | succ k ih =>
      have hblk := X_pow_dvd_borweinBlock_sub_one R N k
      have hsplit : borweinProduct R (N + k + 1) - borweinProduct R N
          = borweinProduct R (N + k) * (borweinBlock R (N + k) - 1)
            + (borweinProduct R (N + k) - borweinProduct R N) := by
        rw [borweinProduct_succ]
        ring
      show (X : R[X]) ^ (3 * N + 1) ∣ borweinProduct R (N + k + 1) - borweinProduct R N
      rw [hsplit]
      exact dvd_add (dvd_mul_of_dvd_right hblk _) ih

/-- **Finite-product `q`-adic stabilization**: `P_n ≡ P_N (mod q^{3N+1})` for every `N ≤ n`.
Every block with index `≥ N` has both of its nonconstant exponents at least `3N + 1`, so the
whole tail product is `1` modulo `q^{3N+1}`. -/
theorem X_pow_dvd_borweinProduct_sub (R : Type*) [CommRing R] {N n : ℕ} (h : N ≤ n) :
    (X : R[X]) ^ (3 * N + 1) ∣ borweinProduct R n - borweinProduct R N := by
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  exact X_pow_dvd_borweinProduct_sub_aux R N k

/-- Every coefficient of `P_n` in degree at most `3N` already equals the corresponding
coefficient of `P_N`, for every `N ≤ n`. -/
theorem coeff_borweinProduct_stable (R : Type*) [CommRing R] {N n k : ℕ} (hNn : N ≤ n)
    (hk : k ≤ 3 * N) :
    (borweinProduct R n).coeff k = (borweinProduct R N).coeff k := by
  have h := Polynomial.X_pow_dvd_iff.mp (X_pow_dvd_borweinProduct_sub R hNn) k (by omega)
  rwa [coeff_sub, sub_eq_zero] at h

/-! ### The three residue components -/

/-- The residue-`0` component `A_n` of the Borwein product: `[x^r]A_n = [q^{3r}]P_n`. -/
noncomputable def borweinA (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  contract 3 (borweinProduct R n)

/-- The residue-`1` component `B_n` of the Borwein product: `[x^r]B_n = -[q^{3r+1}]P_n`.
The sign is the printed normalization `P_n(q) = A_n(q^3) - q B_n(q^3) - q^2 C_n(q^3)`; it is
*not* an assertion about the sign of the coefficients. -/
noncomputable def borweinB (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  -contract 3 (divX (borweinProduct R n))

/-- The residue-`2` component `C_n` of the Borwein product: `[x^r]C_n = -[q^{3r+2}]P_n`,
with the same sign convention as `borweinB`. -/
noncomputable def borweinC (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  -contract 3 (divX (divX (borweinProduct R n)))

/-- Unfolding lemma for `borweinA`. -/
theorem borweinA_def (R : Type*) [CommRing R] (n : ℕ) :
    borweinA R n = contract 3 (borweinProduct R n) := rfl

/-- Unfolding lemma for `borweinB`. -/
theorem borweinB_def (R : Type*) [CommRing R] (n : ℕ) :
    borweinB R n = -contract 3 (divX (borweinProduct R n)) := rfl

/-- Unfolding lemma for `borweinC`. -/
theorem borweinC_def (R : Type*) [CommRing R] (n : ℕ) :
    borweinC R n = -contract 3 (divX (divX (borweinProduct R n))) := rfl

/-- `a_{n,r} = [q^{3r}] P_n`. -/
theorem coeff_borweinA (R : Type*) [CommRing R] (n r : ℕ) :
    (borweinA R n).coeff r = (borweinProduct R n).coeff (3 * r) := by
  have h3 : (3 : ℕ) ≠ 0 := by omega
  rw [borweinA_def, coeff_contract h3]
  exact congrArg (fun i => (borweinProduct R n).coeff i) (by ring)

/-- `b_{n,r} = -[q^{3r+1}] P_n`. -/
theorem coeff_borweinB (R : Type*) [CommRing R] (n r : ℕ) :
    (borweinB R n).coeff r = -(borweinProduct R n).coeff (3 * r + 1) := by
  have h3 : (3 : ℕ) ≠ 0 := by omega
  rw [borweinB_def, coeff_neg, coeff_contract h3, coeff_divX]
  exact congrArg (fun i => -(borweinProduct R n).coeff i) (by ring)

/-- `c_{n,r} = -[q^{3r+2}] P_n`. -/
theorem coeff_borweinC (R : Type*) [CommRing R] (n r : ℕ) :
    (borweinC R n).coeff r = -(borweinProduct R n).coeff (3 * r + 2) := by
  have h3 : (3 : ℕ) ≠ 0 := by omega
  rw [borweinC_def, coeff_neg, coeff_contract h3, coeff_divX, coeff_divX]
  exact congrArg (fun i => -(borweinProduct R n).coeff i) (by ring)

/-- `A_n` has degree at most `n^2`. -/
theorem natDegree_borweinA_le (R : Type*) [CommRing R] (n : ℕ) :
    (borweinA R n).natDegree ≤ n ^ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_borweinA]
  exact coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_borweinProduct_le R n) (by omega))

/-- `B_n` has degree at most `n^2 - 1` (this also holds at `n = 0`, where `B_0 = 0`). -/
theorem natDegree_borweinB_le (R : Type*) [CommRing R] (n : ℕ) :
    (borweinB R n).natDegree ≤ n ^ 2 - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hz : (borweinProduct R n).coeff (3 * N + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_borweinProduct_le R n) (by omega))
  rw [coeff_borweinB, hz, neg_zero]

/-- `C_n` has degree at most `n^2 - 1` (this also holds at `n = 0`, where `C_0 = 0`). -/
theorem natDegree_borweinC_le (R : Type*) [CommRing R] (n : ℕ) :
    (borweinC R n).natDegree ≤ n ^ 2 - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hz : (borweinProduct R n).coeff (3 * N + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_borweinProduct_le R n) (by omega))
  rw [coeff_borweinC, hz, neg_zero]

/-! ### The defining dissection -/

/-- Reading the coefficient of `X^s · f(X^3)` in a degree of residue `s` modulo `3`. -/
theorem coeff_X_pow_mul_expand (R : Type*) [CommRing R] (f : R[X]) (s r : ℕ) :
    ((X : R[X]) ^ s * expand R 3 f).coeff (3 * r + s) = f.coeff r := by
  have hp : (0 : ℕ) < 3 := by omega
  have hle : s ≤ 3 * r + s := by omega
  have hsub : 3 * r + s - s = 3 * r := by omega
  rw [coeff_X_pow_mul', if_pos hle, hsub, coeff_expand_mul' hp]

/-- `X^s · f(X^3)` has no coefficient outside the residue class `s` modulo `3`. -/
theorem coeff_X_pow_mul_expand_of_ne (R : Type*) [CommRing R] (f : R[X]) (s k : ℕ)
    (hs : s < 3) (hne : k % 3 ≠ s) :
    ((X : R[X]) ^ s * expand R 3 f).coeff k = 0 := by
  have hp : (0 : ℕ) < 3 := by omega
  rw [coeff_X_pow_mul']
  split_ifs with hle
  · have h3 : ¬ (3 ∣ k - s) := by
      rintro ⟨c, hc⟩
      omega
    rw [coeff_expand hp, if_neg h3]
  · rfl

set_option maxHeartbeats 800000 in
/-- **The Borwein dissection**:

`P_n(q) = A_n(q^3) - q B_n(q^3) - q^2 C_n(q^3)`.

The three components are not postulated: they are the residue-class contractions of `P_n`,
and this theorem says that they really do reassemble `P_n` with the printed signs. -/
theorem borweinProduct_dissection (R : Type*) [CommRing R] (n : ℕ) :
    borweinProduct R n
      = expand R 3 (borweinA R n) - X * expand R 3 (borweinB R n)
        - X ^ 2 * expand R 3 (borweinC R n) := by
  have hA0 : expand R 3 (borweinA R n) = (X : R[X]) ^ 0 * expand R 3 (borweinA R n) := by
    rw [pow_zero, one_mul]
  have hB1 : (X : R[X]) * expand R 3 (borweinB R n)
      = (X : R[X]) ^ 1 * expand R 3 (borweinB R n) := by
    rw [pow_one]
  rw [hA0, hB1]
  ext k
  rw [coeff_sub, coeff_sub]
  obtain ⟨r, hr⟩ : ∃ r, k = 3 * r + k % 3 := ⟨k / 3, by omega⟩
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · have hk : k = 3 * r + 0 := by omega
    rw [hk]
    rw [coeff_X_pow_mul_expand R (borweinA R n) 0 r,
      coeff_X_pow_mul_expand_of_ne R (borweinB R n) 1 (3 * r + 0) (by omega) (by omega),
      coeff_X_pow_mul_expand_of_ne R (borweinC R n) 2 (3 * r + 0) (by omega) (by omega),
      coeff_borweinA]
    simp
  · have hk : k = 3 * r + 1 := by omega
    rw [hk]
    rw [coeff_X_pow_mul_expand_of_ne R (borweinA R n) 0 (3 * r + 1) (by omega) (by omega),
      coeff_X_pow_mul_expand R (borweinB R n) 1 r,
      coeff_X_pow_mul_expand_of_ne R (borweinC R n) 2 (3 * r + 1) (by omega) (by omega),
      coeff_borweinB]
    simp
  · have hk : k = 3 * r + 2 := by omega
    rw [hk]
    rw [coeff_X_pow_mul_expand_of_ne R (borweinA R n) 0 (3 * r + 2) (by omega) (by omega),
      coeff_X_pow_mul_expand_of_ne R (borweinB R n) 1 (3 * r + 2) (by omega) (by omega),
      coeff_X_pow_mul_expand R (borweinC R n) 2 r,
      coeff_borweinC]
    simp

/-! ### Reciprocity -/

/-- **Reciprocity for `A_n`, coefficient form**: `a_{n,r} = a_{n,s}` whenever `r + s = n^2`. -/
theorem coeff_borweinA_rev (R : Type*) [CommRing R] {n r s : ℕ} (h : r + s = n ^ 2) :
    (borweinA R n).coeff r = (borweinA R n).coeff s := by
  rw [coeff_borweinA, coeff_borweinA]
  exact coeff_borweinProduct_rev R (by omega)

/-- **Reciprocity `B ↦ C`, coefficient form**: `b_{n,r} = c_{n,s}` whenever `r + s + 1 = n^2`. -/
theorem coeff_borweinB_rev (R : Type*) [CommRing R] {n r s : ℕ} (h : r + s + 1 = n ^ 2) :
    (borweinB R n).coeff r = (borweinC R n).coeff s := by
  rw [coeff_borweinB, coeff_borweinC]
  exact neg_inj.mpr (coeff_borweinProduct_rev R (by omega))

/-- **Reciprocity `C ↦ B`, coefficient form**: `c_{n,r} = b_{n,s}` whenever `r + s + 1 = n^2`. -/
theorem coeff_borweinC_rev (R : Type*) [CommRing R] {n r s : ℕ} (h : r + s + 1 = n ^ 2) :
    (borweinC R n).coeff r = (borweinB R n).coeff s := by
  rw [coeff_borweinC, coeff_borweinB]
  exact neg_inj.mpr (coeff_borweinProduct_rev R (by omega))

/-- **`A_n(x) = x^{n^2} A_n(1/x)`**, the first printed reciprocity identity.
Recall that `Polynomial.reflect N f` is exactly `x^N f(1/x)` for `f.natDegree ≤ N`.
No hypothesis on `n` is needed: at `n = 0` both sides are `1`. -/
theorem reflect_borweinA (R : Type*) [CommRing R] (n : ℕ) :
    reflect (n ^ 2) (borweinA R n) = borweinA R n := by
  refine reflect_eq_of_coeff_rev (natDegree_borweinA_le R n) (natDegree_borweinA_le R n) ?_
  intro i hi
  exact coeff_borweinA_rev R (by omega)

/-- **`C_n(x) = x^{n^2-1} B_n(1/x)`**, the third printed reciprocity identity, read as a
reflection of `B_n`.  The hypothesis `1 ≤ n` is the printed one; at `n = 0` the truncated
index `n^2 - 1` degenerates and the coefficient comparison below is unavailable. -/
theorem reflect_borweinB (R : Type*) [CommRing R] {n : ℕ} (hn : 1 ≤ n) :
    reflect (n ^ 2 - 1) (borweinB R n) = borweinC R n := by
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  refine reflect_eq_of_coeff_rev (natDegree_borweinB_le R n) (natDegree_borweinC_le R n) ?_
  intro i hi
  exact coeff_borweinB_rev R (by omega)

/-- **`B_n(x) = x^{n^2-1} C_n(1/x)`**, the second printed reciprocity identity, read as a
reflection of `C_n`. -/
theorem reflect_borweinC (R : Type*) [CommRing R] {n : ℕ} (hn : 1 ≤ n) :
    reflect (n ^ 2 - 1) (borweinC R n) = borweinB R n := by
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  refine reflect_eq_of_coeff_rev (natDegree_borweinC_le R n) (natDegree_borweinB_le R n) ?_
  intro i hi
  exact coeff_borweinC_rev R (by omega)

/-! ### The two "in particular" corollaries -/

/-- `P_n(1) = 0` for `n ≥ 1`: the block of index `0` contains the factor `1 - X`. -/
theorem eval_one_borweinProduct (R : Type*) [CommRing R] {n : ℕ} (hn : 1 ≤ n) :
    (borweinProduct R n).eval 1 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : (borweinBlock R 0).eval (1 : R) = 0 := by
    rw [borweinBlock_def]
    simp
  rw [borweinProduct_def, Finset.prod_range_succ', eval_mul, hb, mul_zero]

/-- **`B_n(1) = C_n(1)`** for `n ≥ 1`: reversing a coefficient sequence does not change its
sum, and `B_n` reversed is `C_n`. -/
theorem eval_one_borweinB_eq_borweinC (R : Type*) [CommRing R] {n : ℕ} (hn : 1 ≤ n) :
    (borweinB R n).eval 1 = (borweinC R n).eval 1 := by
  rw [← reflect_borweinB R hn, eval_one_reflect (natDegree_borweinB_le R n)]

/-- **`A_n(1) = 2 B_n(1)`** for `n ≥ 1`: evaluate the dissection at `q = 1`, where
`P_n(1) = 0` gives `A_n(1) = B_n(1) + C_n(1)`, and combine with `B_n(1) = C_n(1)`. -/
theorem eval_one_borweinA (R : Type*) [CommRing R] {n : ℕ} (hn : 1 ≤ n) :
    (borweinA R n).eval 1 = 2 * (borweinB R n).eval 1 := by
  have hP : (borweinProduct R n).eval 1 = 0 := eval_one_borweinProduct R hn
  have hBC : (borweinB R n).eval 1 = (borweinC R n).eval 1 :=
    eval_one_borweinB_eq_borweinC R hn
  have hd : (borweinProduct R n).eval (1 : R)
      = (expand R 3 (borweinA R n) - X * expand R 3 (borweinB R n)
          - X ^ 2 * expand R 3 (borweinC R n)).eval (1 : R) := by
    rw [borweinProduct_dissection R n]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, one_pow, one_mul, expand_eval] at hd
  rw [hP] at hd
  have hsum : (borweinA R n).eval 1
      = (borweinB R n).eval 1 + (borweinC R n).eval 1 := by
    calc (borweinA R n).eval 1
        = ((borweinA R n).eval 1 - (borweinB R n).eval 1 - (borweinC R n).eval 1)
          + (borweinB R n).eval 1 + (borweinC R n).eval 1 := by ring
      _ = 0 + (borweinB R n).eval 1 + (borweinC R n).eval 1 := by rw [← hd]
      _ = (borweinB R n).eval 1 + (borweinC R n).eval 1 := by ring
  rw [hsum, ← hBC]
  ring

/-! ### Two-ended stabilization -/

/-- **Lower-end stabilization for `A`**: `a_{n,d} = a_{d+1,d}` for every `n ≥ d + 1`.
The exponent `3d` lies below the stabilization threshold `3(d+1) + 1 = 3d + 4`. -/
theorem coeff_borweinA_stabilize (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinA R n).coeff d = (borweinA R (d + 1)).coeff d := by
  rw [coeff_borweinA, coeff_borweinA]
  exact coeff_borweinProduct_stable R h (by omega)

/-- **Lower-end stabilization for `B`**: `b_{n,d} = b_{d+1,d}` for every `n ≥ d + 1`. -/
theorem coeff_borweinB_stabilize (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinB R n).coeff d = (borweinB R (d + 1)).coeff d := by
  rw [coeff_borweinB, coeff_borweinB]
  exact neg_inj.mpr (coeff_borweinProduct_stable R h (by omega))

/-- **Lower-end stabilization for `C`**: `c_{n,d} = c_{d+1,d}` for every `n ≥ d + 1`. -/
theorem coeff_borweinC_stabilize (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinC R n).coeff d = (borweinC R (d + 1)).coeff d := by
  rw [coeff_borweinC, coeff_borweinC]
  exact neg_inj.mpr (coeff_borweinProduct_stable R h (by omega))

/-- **Upper-end stabilization for `A`**: `a_{n,n^2-d} = a_{d+1,d}` for every `n ≥ d + 1`. -/
theorem coeff_borweinA_top (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinA R n).coeff (n ^ 2 - d) = (borweinA R (d + 1)).coeff d := by
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  rw [coeff_borweinA_rev R (show n ^ 2 - d + d = n ^ 2 from by omega)]
  exact coeff_borweinA_stabilize R h

/-- **Upper-end stabilization for `B`**: `b_{n,n^2-1-d} = c_{d+1,d}` for every `n ≥ d + 1`. -/
theorem coeff_borweinB_top (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinB R n).coeff (n ^ 2 - 1 - d) = (borweinC R (d + 1)).coeff d := by
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  rw [coeff_borweinB_rev R (show n ^ 2 - 1 - d + d + 1 = n ^ 2 from by omega)]
  exact coeff_borweinC_stabilize R h

/-- **Upper-end stabilization for `C`**: `c_{n,n^2-1-d} = b_{d+1,d}` for every `n ≥ d + 1`. -/
theorem coeff_borweinC_top (R : Type*) [CommRing R] {d n : ℕ} (h : d + 1 ≤ n) :
    (borweinC R n).coeff (n ^ 2 - 1 - d) = (borweinB R (d + 1)).coeff d := by
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  rw [coeff_borweinC_rev R (show n ^ 2 - 1 - d + d + 1 = n ^ 2 from by omega)]
  exact coeff_borweinB_stabilize R h

/-! ### The quotient normalization of the Borwein product

The printed definition is `P_n(q) = (q;q)_{3n}/(q^3;q^3)_n`.  Division is avoided by stating
the equivalent product identity `(q;q)_{3n} = P_n(q) · (q^3;q^3)_n`, which holds over an
arbitrary commutative ring and for an arbitrary ring element `q` — no invertibility and no
nonvanishing hypothesis. -/

/-- Trisecting `(q;q)_{3n}` by the residue of the factor index modulo `3`:

`(q;q)_{3n} = (∏_{j<n} (1 - q^{3j+1})(1 - q^{3j+2})) · (q^3;q^3)_n`.

At `q = X` the middle factor is the Borwein product. -/
theorem finiteQPochhammerIn_three_mul {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    finiteQPochhammerIn q q (3 * n)
      = (∏ j ∈ Finset.range n, (1 - q ^ (3 * j + 1)) * (1 - q ^ (3 * j + 2)))
        * finiteQPochhammerIn (q ^ 3) (q ^ 3) n := by
  have hdef : ∀ (a Q : R) (m : ℕ),
      finiteQPochhammerIn a Q m = ∏ j ∈ Finset.range m, (1 - a * Q ^ j) := fun _ _ _ => rfl
  have hpow : ∀ j : ℕ, (q ^ 3) ^ j = q ^ (3 * j) := fun j => (pow_mul q 3 j).symm
  have e0 : finiteQPochhammerIn (q * q ^ 0) (q ^ 3) n
      = ∏ j ∈ Finset.range n, (1 - q ^ (3 * j + 1)) := by
    rw [hdef]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hpow]
    ring
  have e1 : finiteQPochhammerIn (q * q ^ 1) (q ^ 3) n
      = ∏ j ∈ Finset.range n, (1 - q ^ (3 * j + 2)) := by
    rw [hdef]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hpow]
    ring
  have e2 : finiteQPochhammerIn (q * q ^ 2) (q ^ 3) n
      = finiteQPochhammerIn (q ^ 3) (q ^ 3) n := by
    rw [show q * q ^ 2 = q ^ 3 from by ring]
  have hsplit : (∏ s ∈ Finset.range 3, finiteQPochhammerIn (q * q ^ s) (q ^ 3) n)
      = finiteQPochhammerIn (q * q ^ 0) (q ^ 3) n
        * finiteQPochhammerIn (q * q ^ 1) (q ^ 3) n
        * finiteQPochhammerIn (q * q ^ 2) (q ^ 3) n := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
  rw [finiteQPochhammerIn_dissection q q 3 n, hsplit, e0, e1, e2, Finset.prod_mul_distrib]

/-- The division-free form of the printed definition `P_n(q) = (q;q)_{3n}/(q^3;q^3)_n`,
specialised to the polynomial variable: `(X;X)_{3n} = P_n(X) · (X^3;X^3)_n`. -/
theorem finiteQPochhammerIn_three_mul_X (R : Type*) [CommRing R] (n : ℕ) :
    finiteQPochhammerIn (X : R[X]) X (3 * n)
      = borweinProduct R n * finiteQPochhammerIn ((X : R[X]) ^ 3) (X ^ 3) n :=
  finiteQPochhammerIn_three_mul (X : R[X]) n

end Fabius
