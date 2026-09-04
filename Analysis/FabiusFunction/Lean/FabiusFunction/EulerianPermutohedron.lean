import FabiusFunction.EulerianPolynomialRecurrence
import FabiusFunction.EulerianStirling
import FabiusFunction.TypeBEulerian

/-!
# Eulerian numbers as face and volume data of polytopes

The Eulerian triangles are the `h`-vectors of the two permutohedra and the
normalized volumes of the half-open hypersimplices.  This module formalizes the
*algebraic* content of the three geometric statements of the manuscript
`Combinatorial_Coefficient_Calculus`; the geometry itself (face lattices,
shellings, Lebesgue measure) is not in scope, and exactly which step is left
outside is spelled out below.

## What is proved

* **`thm:permutohedron-h-polynomial`** — the type-`A` permutohedron `P_n`, the
  convex hull of the permutations of `(1, …, n)`, has a nonempty face for each
  ordered set partition of `[n]`; a partition into `k` blocks gives a face of
  dimension `n - k`, and there are `permutohedronFaceNumber n k = k! S(n,k)` of
  them.  For a simple polytope the `h`-polynomial is the face transform
  `h_P(t) = ∑_{∅ ≠ F ≤ P} (t-1)^{dim F}`, so the theorem is the identity
  `∑_{k ≤ n} k! S(n,k) (t-1)^{n-k} = A_n(t)`
  (`sum_permutohedronFaceNumber_mul_X_sub_one_pow` in `R⟦X⟧`,
  `permutohedron_h_polynomial` in `Polynomial R`), together with its
  coefficientwise form `permutohedron_h_vector`, which says `h_j = A(n,j)`.

* **`thm:eulerian-irwin-hall`** — the *combinatorial core*.  Inclusion–exclusion
  gives `n! · vol{x ∈ [0,1]^n : ∑ xᵢ < y} = ∑_{j ≤ y} (-1)^j C(n,j) (y-j)^n` for
  an integer `y`; that alternating sum is `cubeSliceCount n y`, and
  `cubeSliceCount_succ_sub` proves
  `cubeSliceCount n (k+1) - cubeSliceCount n k = A(n,k)` for `n ≥ 1`, i.e. that
  the `k`-th half-open hypersimplex has normalized volume `A(n,k)`.  The
  telescoped statements `cubeSliceCount_eq_sum_eulerianNumber` and
  `cubeSliceCount_self` (`= n!`, the whole cube) come with it.

* **`thm:typeB-permutohedron-h-polynomial`** — the type-`B` permutohedron has,
  in dimension `n - k`, exactly `typeBFaceNumber n k` faces (signed ordered set
  partitions of `[n]` with a possibly empty zero block), defined here by the
  finite-difference recurrence `T(n+1,k) = (2k+1) T(n,k) + 2k T(n,k-1)`.  The
  `h`-polynomial of the simplicial polar is the standard `f`-to-`h` transform
  `h(t) = ∑_i f_{i-1} t^i (1-t)^{d-i}`, and
  `sum_typeBEulerian_mul_X_pow_eq_sum_typeBFaceNumber` proves
  `∑_{k ≤ n} T(n,k) t^k (1-t)^{n-k} = B_n(t)`.
  The engine is the sign-free type-`B` Newton expansion
  `typeB_newton : (2m+1)^n = ∑_{k ≤ n} T(n,k) C(m,k)`, which characterizes `T`
  and identifies it as the `k`-th forward difference of `j ↦ (2j+1)^n` at `0` —
  the exact type-`B` analogue of `k! S(n,k) = Δ^k (j ↦ j^n)(0)`.

## What is *not* proved

* **No geometry.**  Nothing here mentions a polytope, a face lattice, a fan, a
  shelling or a Coxeter group.  What is formalized is the identity that the
  manuscript's geometric argument reduces to, once the face numbers are known.
  Supplying "`P_n` has `k! S(n,k)` faces of dimension `n-k`", "the type-`B`
  permutohedron has `T(n,k)` faces of dimension `n-k`", and the two standard
  `f`-to-`h` transforms would upgrade these to the manuscript's statements.

* **No measure theory.**  `cubeSliceCount` is the inclusion–exclusion *number*,
  not a Lebesgue integral.  Closing `thm:eulerian-irwin-hall` completely needs
  `volume {x : Fin n → ℝ | (∀ i, x i ∈ Icc 0 1) ∧ ∑ i, x i < y} =
  cubeSliceCount n y / n!`, an induction on `n` with Fubini over the cube that
  Mathlib does not currently supply; the summation form of the theorem, i.e.
  `∑_k A(n,k) f(k) = n! ∫ f(⌊∑ xᵢ⌋)`, is then pure telescoping.

* The `T(n,k)` recurrence is *taken as the definition* of the type-`B` face
  numbers, exactly as `TypeBEulerian` takes the recurrence as the definition of
  `B(n,k)`.  The signed-permutation and signed-set-partition interpretations are
  not formalized.

## Two normalizations, deliberately

The type-`A` statement uses the simple-polytope transform `∑ f_i (t-1)^i` (the
form the manuscript displays) and the type-`B` statement the simplicial
transform `∑ f_{i-1} t^i (1-t)^{d-i}` (the form its "boundary complex of the
simplicial polar" phrasing invokes).  The two differ by reversing the
coefficient list, so they agree exactly because both Eulerian rows are
palindromic; each is proved here in the shape in which its Newton expansion is
sign-free, which is why they are not stated alike.

## An observation the formalization exposes

The two types run on *different* Newton expansions: type `A` uses the shifted
binomial basis `C(m+k, k)`, whose generating function is `(1-t)^{-(k+1)}`, and
type `B` the plain basis `C(m,k)`, whose generating function is
`t^k (1-t)^{-(k+1)}`.  That single `t^k` is the whole difference between the two
`f`-to-`h` transforms above.  Also, `permutohedronFaceNumber n k` is by
definition the summand of `Fabius.fubini n`: the total number of nonempty faces
of `P_n` is the `n`-th ordered Bell number.

## Main results

* `permutohedronFaceNumber`, `permutohedronFaceNumber_self`,
  `permutohedronFaceNumber_one`.
* `sum_permutohedronFaceNumber_mul_X_sub_one_pow`, `permutohedron_h_polynomial`,
  `permutohedron_h_vector`.
* `cubeSliceCount`, `cubeSliceCount_zero`, `cubeSliceCount_succ_sub`,
  `cubeSliceCount_eq_sum_eulerianNumber`, `cubeSliceCount_self`.
* `typeBFaceNumber`, `typeBFaceNumber_self`, `typeBFaceNumber_one`,
  `typeB_newton`, `oddPowSeries_eq_sum_typeBFaceNumber`,
  `sum_typeBEulerian_mul_X_pow_eq_sum_typeBFaceNumber`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### A coefficient formula used throughout -/

section

variable (R : Type*) [CommRing R]

/-- The coefficients of `(X - 1)^N`: `[X^i] (X-1)^N = (-1)^{N+i} C(N,i)`. -/
theorem coeff_X_sub_one_pow (N i : ℕ) :
    PowerSeries.coeff i ((X - 1 : R⟦X⟧) ^ N) = (-1) ^ (N + i) * (N.choose i : R) := by
  have hsign : ((X : R⟦X⟧) - 1) ^ N = (-1 : R⟦X⟧) ^ N * (1 - X) ^ N := by
    rw [← neg_sub, neg_pow]
  have hpow : ((-1 : R⟦X⟧)) ^ N = PowerSeries.C ((-1 : R) ^ N) := by
    simp
  rw [hsign, hpow, coeff_C_mul, coeff_one_sub_X_pow, pow_add]
  ring

end

/-! ### The type-A permutohedron -/

/-- The number of faces of dimension `n - k` of the type-`A` permutohedron `P_n`,
the convex hull of the permutations of `(1, …, n)`.  A nonempty face of `P_n` is
indexed by an ordered set partition of `[n]`; a partition into `k` nonempty
blocks gives a face of dimension `n - k`, and there are `k! S(n,k)` of them.  So
`k = 1` is the polytope itself, of dimension `n - 1`, and `k = n` counts the
vertices.  Summed over `k` this is `Fabius.fubini n`, the ordered Bell number. -/
def permutohedronFaceNumber (n k : ℕ) : ℕ := k.factorial * Nat.stirlingSecond n k

/-- `P_n` has `n!` vertices: its `0`-dimensional faces are the ordered partitions
of `[n]` into `n` singletons. -/
@[simp] theorem permutohedronFaceNumber_self (n : ℕ) :
    permutohedronFaceNumber n n = n.factorial := by
  simp only [permutohedronFaceNumber, Nat.stirlingSecond_self, mul_one]

/-- `P_{n+1}` is its own unique face of dimension `n`. -/
theorem permutohedronFaceNumber_one (n : ℕ) : permutohedronFaceNumber (n + 1) 1 = 1 := by
  simp only [permutohedronFaceNumber, Nat.stirlingSecond_one_right, Nat.factorial_one, mul_one]

section

variable (R : Type*) [CommRing R]

/-- **The permutohedral `h`-polynomial** (`thm:permutohedron-h-polynomial`), in
`R⟦X⟧`: the face transform `∑_{∅ ≠ F ≤ P_n} (t-1)^{dim F}` of the simple
polytope `P_n` is the Eulerian polynomial,
`∑_{k ≤ n} k! S(n,k) (t-1)^{n-k} = ∑_{k ≤ n} A(n,k) t^k`. -/
theorem sum_permutohedronFaceNumber_mul_X_sub_one_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (permutohedronFaceNumber n k : R⟦X⟧) * (X - 1) ^ (n - k) =
      ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k := by
  rw [sum_eulerianNumber_mul_X_pow_eq_sum_stirlingSecond R n]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [permutohedronFaceNumber]
  rw [Nat.mul_comm k.factorial (Nat.stirlingSecond n k),
    map_natCast (PowerSeries.C : R →+* R⟦X⟧)]

/-- **The permutohedral `h`-polynomial** as an identity of polynomials:
`∑_{k ≤ n} k! S(n,k) (X-1)^{n-k} = A_n(X)`. -/
theorem permutohedron_h_polynomial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (permutohedronFaceNumber n k : Polynomial R) * (Polynomial.X - 1) ^ (n - k) =
      eulerianPolynomial R n := by
  refine Polynomial.coe_injective R ?_
  have hL : ((∑ k ∈ Finset.range (n + 1),
        (permutohedronFaceNumber n k : Polynomial R) * (Polynomial.X - 1) ^ (n - k) :
          Polynomial R) : R⟦X⟧)
      = ∑ k ∈ Finset.range (n + 1),
          (permutohedronFaceNumber n k : R⟦X⟧) * (X - 1) ^ (n - k) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, map_sub, map_one, map_natCast,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  have hR : ((eulerianPolynomial R n : Polynomial R) : R⟦X⟧)
      = ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k := by
    simp only [eulerianPolynomial]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, map_natCast, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X]
  rw [hL, hR]
  exact sum_permutohedronFaceNumber_mul_X_sub_one_pow R n

end

/-- **The permutohedral `h`-vector:** reading the face transform coefficient by
coefficient, `h_j = ∑_{k ≤ n} (-1)^{n-k+j} C(n-k, j) k! S(n,k) = A(n,j)`, for
every `j` (both sides vanish for `j > n`). -/
theorem permutohedron_h_vector (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n - k + j) * ((n - k).choose j : ℤ) * (permutohedronFaceNumber n k : ℤ)
      = (eulerianNumber n j : ℤ) := by
  have h := congrArg (PowerSeries.coeff j)
    (sum_permutohedronFaceNumber_mul_X_sub_one_pow ℤ n)
  simp only [map_sum] at h
  have hL : ∀ k : ℕ, PowerSeries.coeff j
      ((permutohedronFaceNumber n k : ℤ⟦X⟧) * (X - 1) ^ (n - k))
      = (-1 : ℤ) ^ (n - k + j) * ((n - k).choose j : ℤ)
          * (permutohedronFaceNumber n k : ℤ) := by
    intro k
    rw [← map_natCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧), coeff_C_mul, coeff_X_sub_one_pow]
    ring
  have hR : ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff j ((eulerianNumber n k : ℤ⟦X⟧) * X ^ k) = (eulerianNumber n j : ℤ) := by
    have hc : ∀ i : ℕ, PowerSeries.coeff j ((eulerianNumber n i : ℤ⟦X⟧) * X ^ i)
        = if j = i then (eulerianNumber n i : ℤ) else 0 := by
      intro i
      rw [← map_natCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧), PowerSeries.coeff_C_mul_X_pow]
    simp only [hc, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hj
    · rfl
    · rw [eulerianNumber_eq_zero_of_lt (by omega : n < j), Nat.cast_zero]
  rw [hR] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => (hL k).symm

/-! ### Half-open hypersimplices: the Irwin–Hall slab count -/

/-- The inclusion–exclusion count
`∑_{j ≤ y} (-1)^j C(n,j) (y-j)^n`, which is `n!` times the volume of
`{x ∈ [0,1]^n : x₁ + ⋯ + xₙ < y}` for a natural number `y` (obtained from the
simplex `{xᵢ ≥ 0 : ∑ xᵢ < y}` by inclusion–exclusion over the coordinates that
exceed `1`).  The volume interpretation is *not* formalized; everything below is
about this integer. -/
def cubeSliceCount (n y : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (y + 1), (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((y - j : ℕ) : ℤ) ^ n

/-- The empty slab is empty: `cubeSliceCount n 0 = 0` for `n ≥ 1`. -/
theorem cubeSliceCount_zero (n : ℕ) (hn : 1 ≤ n) : cubeSliceCount n 0 = 0 := by
  simp [cubeSliceCount, zero_pow (show n ≠ 0 by omega)]

/-- **The Irwin–Hall slab identity** (the combinatorial core of
`thm:eulerian-irwin-hall`): the `k`-th half-open hypersimplex
`{x ∈ [0,1]^n : k ≤ ∑ xᵢ < k+1}` has normalized volume `A(n,k)`, i.e.
`cubeSliceCount n (k+1) - cubeSliceCount n k = A(n,k)` whenever `n ≥ 1`.
The hypothesis is necessary: for `n = 0` the left side is `0` and `A(0,0) = 1`. -/
theorem cubeSliceCount_succ_sub (n k : ℕ) (hn : 1 ≤ n) :
    cubeSliceCount n (k + 1) - cubeSliceCount n k = (eulerianNumber n k : ℤ) := by
  have hzero : ((0 : ℕ) : ℤ) ^ n = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega : n ≠ 0)]
  have hA : cubeSliceCount n (k + 1)
      = (∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (i + 1) * (n.choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n)
        + ((k + 1 : ℕ) : ℤ) ^ n := by
    have hp : (∑ j ∈ Finset.range (k + 1 + 1),
          (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n)
        = (∑ i ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ (i + 1) * (n.choose (i + 1) : ℤ) * ((k + 1 - (i + 1) : ℕ) : ℤ) ^ n)
          + (-1 : ℤ) ^ 0 * (n.choose 0 : ℤ) * ((k + 1 - 0 : ℕ) : ℤ) ^ n :=
      Finset.sum_range_succ' _ (k + 1)
    have hq : (∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (i + 1) * (n.choose (i + 1) : ℤ) * ((k + 1 - (i + 1) : ℕ) : ℤ) ^ n)
        = ∑ i ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ (i + 1) * (n.choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n :=
      Finset.sum_congr rfl fun i _ => by
        rw [show k + 1 - (i + 1) = k - i from by omega]
    simp only [cubeSliceCount]
    rw [hp, hq]
    simp
  have hB : cubeSliceCount n k
      = ∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ i * (n.choose i : ℤ) * ((k - i : ℕ) : ℤ) ^ n := by
    simp only [cubeSliceCount]
  have hG : (eulerianNumber n k : ℤ)
      = (∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (i + 1) * ((n + 1).choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n)
        + ((k + 1 : ℕ) : ℤ) ^ n := by
    have hext : (∑ j ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n)
        = ∑ j ∈ Finset.range (k + 1 + 1),
            (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n := by
      have hp : (∑ j ∈ Finset.range (k + 1 + 1),
            (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n)
          = (∑ j ∈ Finset.range (k + 1),
              (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n)
            + (-1 : ℤ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℤ)
                * ((k + 1 - (k + 1) : ℕ) : ℤ) ^ n :=
        Finset.sum_range_succ _ (k + 1)
      rw [hp, show k + 1 - (k + 1) = 0 from by omega, hzero, mul_zero, add_zero]
    have hp' : (∑ j ∈ Finset.range (k + 1 + 1),
          (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) * ((k + 1 - j : ℕ) : ℤ) ^ n)
        = (∑ i ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ (i + 1) * ((n + 1).choose (i + 1) : ℤ)
              * ((k + 1 - (i + 1) : ℕ) : ℤ) ^ n)
          + (-1 : ℤ) ^ 0 * ((n + 1).choose 0 : ℤ) * ((k + 1 - 0 : ℕ) : ℤ) ^ n :=
      Finset.sum_range_succ' _ (k + 1)
    have hq : (∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (i + 1) * ((n + 1).choose (i + 1) : ℤ)
            * ((k + 1 - (i + 1) : ℕ) : ℤ) ^ n)
        = ∑ i ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ (i + 1) * ((n + 1).choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n :=
      Finset.sum_congr rfl fun i _ => by
        rw [show k + 1 - (i + 1) = k - i from by omega]
    rw [eulerianNumber_eq_sum_int, hext, hp', hq]
    simp
  have hsum : (∑ i ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (i + 1) * (n.choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n)
      = (∑ i ∈ Finset.range (k + 1),
          (-1 : ℤ) ^ (i + 1) * ((n + 1).choose (i + 1) : ℤ) * ((k - i : ℕ) : ℤ) ^ n)
        + ∑ i ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ i * (n.choose i : ℤ) * ((k - i : ℕ) : ℤ) ^ n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.choose_succ_succ' n i]
    push_cast
    ring
  rw [hA, hB, hG, hsum]
  ring

/-- Telescoping the slab identity: `cubeSliceCount n N = ∑_{k < N} A(n,k)` for
`n ≥ 1`.  Geometrically, the volume of `{x ∈ [0,1]^n : ∑ xᵢ < N}` is the sum of
the volumes of the slabs below `N`. -/
theorem cubeSliceCount_eq_sum_eulerianNumber (n N : ℕ) (hn : 1 ≤ n) :
    cubeSliceCount n N = ∑ k ∈ Finset.range N, (eulerianNumber n k : ℤ) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_zero]
    exact cubeSliceCount_zero n hn
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, ← cubeSliceCount_succ_sub n N hn]
    ring

/-- The whole cube: `cubeSliceCount n n = n!`, the normalized statement that
`[0,1]^n` has volume `1` and that the Eulerian row sums to `n!`. -/
theorem cubeSliceCount_self (n : ℕ) (hn : 1 ≤ n) :
    cubeSliceCount n n = (n.factorial : ℤ) := by
  rw [cubeSliceCount_eq_sum_eulerianNumber n n hn]
  have h := sum_eulerianNumber_eq_factorial n
  rw [Finset.sum_range_succ, eulerianNumber_eq_zero_of_le hn le_rfl, add_zero] at h
  exact_mod_cast h

/-! ### The type-B permutohedron -/

/-- The number of faces of dimension `n - k` of the type-`B` permutohedron, the
convex hull of the signed permutations of `(1, …, n)`, defined by the
finite-difference recurrence `T(n+1,k) = (2k+1) T(n,k) + 2k T(n,k-1)` with
`T(0,0) = 1`.  Equivalently `T(n,k) = Δ^k (j ↦ (2j+1)^n)(0)`, the type-`B`
analogue of `k! S(n,k) = Δ^k (j ↦ j^n)(0)`; combinatorially it counts the signed
ordered set partitions of `[n]` into `k` blocks with a (possibly empty) zero
block.  `k = 0` is the polytope itself, of dimension `n`; `k = 1` counts the
facets and `k = n` the vertices. -/
def typeBFaceNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      (2 * k + 3) * typeBFaceNumber n (k + 1) + (2 * k + 2) * typeBFaceNumber n k

/-- The type-`B` face triangle starts at `1`. -/
@[simp] theorem typeBFaceNumber_zero_zero : typeBFaceNumber 0 0 = 1 := rfl

/-- Row `0` of the type-`B` face triangle vanishes beyond its first entry. -/
@[simp] theorem typeBFaceNumber_zero_succ (k : ℕ) : typeBFaceNumber 0 (k + 1) = 0 := rfl

/-- Column `0` is constant: the polytope is its own unique top-dimensional face. -/
@[simp] theorem typeBFaceNumber_zero_right (n : ℕ) : typeBFaceNumber n 0 = 1 := by
  cases n <;> rfl

/-- The defining recurrence, in the shifted indexing
`T(n+1,k+1) = (2k+3) T(n,k+1) + (2k+2) T(n,k)`. -/
theorem typeBFaceNumber_succ_succ (n k : ℕ) :
    typeBFaceNumber (n + 1) (k + 1) =
      (2 * k + 3) * typeBFaceNumber n (k + 1) + (2 * k + 2) * typeBFaceNumber n k := rfl

/-- There are no faces of negative dimension: `T(n,k) = 0` for `n < k`. -/
theorem typeBFaceNumber_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → typeBFaceNumber n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [typeBFaceNumber_succ_succ, typeBFaceNumber_eq_zero_of_lt (show n < k + 1 by omega),
      typeBFaceNumber_eq_zero_of_lt (show n < k by omega), mul_zero, mul_zero, add_zero]

/-- The type-`B` permutohedron has `2^n n!` vertices, one for each signed
permutation. -/
theorem typeBFaceNumber_self (n : ℕ) : typeBFaceNumber n n = 2 ^ n * n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typeBFaceNumber_succ_succ, typeBFaceNumber_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero,
      zero_add, ih, Nat.factorial_succ, pow_succ]
    ring

/-- The type-`B` permutohedron has `3^n - 1` facets, stated without truncated
subtraction as `T(n,1) + 1 = 3^n`. -/
theorem typeBFaceNumber_one (n : ℕ) : typeBFaceNumber n 1 + 1 = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrec : typeBFaceNumber (n + 1) 1
        = (2 * 0 + 3) * typeBFaceNumber n 1 + (2 * 0 + 2) * typeBFaceNumber n 0 :=
      typeBFaceNumber_succ_succ n 0
    rw [hrec, typeBFaceNumber_zero_right, pow_succ, ← ih]
    ring

/-- The one-step relation behind the type-`B` Newton expansion:
`(2m+1) C(m,k) = 2(k+1) C(m,k+1) + (2k+1) C(m,k)`. -/
theorem two_mul_add_one_mul_choose' (m k : ℕ) :
    (2 * m + 1) * m.choose k = 2 * (k + 1) * m.choose (k + 1) + (2 * k + 1) * m.choose k := by
  rcases Nat.lt_or_ge m k with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]
    simp
  · have hc := Nat.choose_succ_right_eq m k
    zify [h] at hc ⊢
    linear_combination (-2 : ℤ) * hc

/-- **The type-`B` Newton expansion:** `(2m+1)^n = ∑_{k ≤ n} T(n,k) C(m,k)`.
This is the sign-free characterization of the type-`B` face numbers, and says
exactly that `T(n,k)` is the `k`-th forward difference of `j ↦ (2j+1)^n` at `0`. -/
theorem typeB_newton (n m : ℕ) :
    (2 * m + 1) ^ n = ∑ k ∈ Finset.range (n + 1), typeBFaceNumber n k * m.choose k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : (2 * m + 1) ^ (n + 1)
        = (∑ k ∈ Finset.range (n + 1), (2 * k + 2) * typeBFaceNumber n k * m.choose (k + 1))
          + ∑ k ∈ Finset.range (n + 1), (2 * k + 1) * typeBFaceNumber n k * m.choose k := by
      rw [pow_succ', ih, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, mul_comm (2 * m + 1) (typeBFaceNumber n k), mul_assoc,
        two_mul_add_one_mul_choose' m k]
      ring
    have hb : (∑ k ∈ Finset.range (n + 1), (2 * k + 1) * typeBFaceNumber n k * m.choose k)
        = (∑ k ∈ Finset.range n,
            (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1)) + 1 := by
      have hp : (∑ k ∈ Finset.range (n + 1),
            (2 * k + 1) * typeBFaceNumber n k * m.choose k)
          = (∑ k ∈ Finset.range n,
              (2 * (k + 1) + 1) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
            + (2 * 0 + 1) * typeBFaceNumber n 0 * m.choose 0 :=
        Finset.sum_range_succ' _ n
      have hq : (∑ k ∈ Finset.range n,
            (2 * (k + 1) + 1) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
          = ∑ k ∈ Finset.range n,
              (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [hp, hq]
      simp
    have hc : (∑ k ∈ Finset.range (n + 1),
          (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
        = ∑ k ∈ Finset.range n,
            (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1) := by
      have hp : (∑ k ∈ Finset.range (n + 1),
            (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
          = (∑ k ∈ Finset.range n,
              (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
            + (2 * n + 3) * typeBFaceNumber n (n + 1) * m.choose (n + 1) :=
        Finset.sum_range_succ _ n
      rw [hp]
      simp [typeBFaceNumber_eq_zero_of_lt (Nat.lt_succ_self n)]
    have hd : (∑ k ∈ Finset.range (n + 1 + 1), typeBFaceNumber (n + 1) k * m.choose k)
        = ((∑ k ∈ Finset.range (n + 1),
              (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
            + ∑ k ∈ Finset.range (n + 1),
                (2 * k + 2) * typeBFaceNumber n k * m.choose (k + 1)) + 1 := by
      have hp : (∑ k ∈ Finset.range (n + 1 + 1), typeBFaceNumber (n + 1) k * m.choose k)
          = (∑ k ∈ Finset.range (n + 1), typeBFaceNumber (n + 1) (k + 1) * m.choose (k + 1))
            + typeBFaceNumber (n + 1) 0 * m.choose 0 :=
        Finset.sum_range_succ' _ (n + 1)
      have hq : (∑ k ∈ Finset.range (n + 1),
            typeBFaceNumber (n + 1) (k + 1) * m.choose (k + 1))
          = (∑ k ∈ Finset.range (n + 1),
              (2 * k + 3) * typeBFaceNumber n (k + 1) * m.choose (k + 1))
            + ∑ k ∈ Finset.range (n + 1),
                (2 * k + 2) * typeBFaceNumber n k * m.choose (k + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [typeBFaceNumber_succ_succ]
        ring
      rw [hp, hq]
      simp
    rw [ha, hd, hb, hc]
    ring

section

variable (R : Type*) [CommRing R]

/-- The type-`B` Newton expansion read column by column, using
`∑_m C(m,k) X^m = X^k (1-X)^{-(k+1)}`. -/
theorem oddPowSeries_eq_sum_typeBFaceNumber (n : ℕ) :
    oddPowSeries R n = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((typeBFaceNumber n k : R)) * (X ^ k * PowerSeries.mk 1 ^ (k + 1)) := by
  ext m
  rw [oddPowSeries, coeff_mk, map_sum]
  have hw : (2 * (m : R) + 1) ^ n = ∑ k ∈ Finset.range (n + 1),
      (typeBFaceNumber n k : R) * (m.choose k : R) := by
    have h := congrArg (Nat.cast : ℕ → R) (typeB_newton n m)
    push_cast at h
    exact h
  rw [hw]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, coeff_X_pow_mul', mk_one_pow_eq_mk_choose_add, coeff_mk]
  split_ifs with h
  · rw [show k + (m - k) = m from by omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k), Nat.cast_zero, mul_zero]

/-- **The type-`B` permutohedral `h`-polynomial**
(`thm:typeB-permutohedron-h-polynomial`): the `f`-to-`h` transform of the
boundary complex of the simplicial polar,
`∑_{k ≤ n} T(n,k) t^k (1-t)^{n-k}`, is the type-`B` Eulerian polynomial
`B_n(t) = ∑_{k ≤ n} B(n,k) t^k`. -/
theorem sum_typeBEulerian_mul_X_pow_eq_sum_typeBFaceNumber (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (typeBEulerian n k : R⟦X⟧) * X ^ k =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((typeBFaceNumber n k : R)) * (X ^ k * (1 - X) ^ (n - k)) := by
  rw [← one_sub_X_pow_mul_oddPowSeries, oddPowSeries_eq_sum_typeBFaceNumber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : ((1 : R⟦X⟧) - X) ^ (n + 1) = (1 - X) ^ (n - k) * (1 - X) ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hunit : ((1 : R⟦X⟧) - X) ^ (k + 1) * PowerSeries.mk 1 ^ (k + 1) = 1 := by
    rw [← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
  calc (1 - X) ^ (n + 1) * (PowerSeries.C ((typeBFaceNumber n k : R)) *
          (X ^ k * PowerSeries.mk 1 ^ (k + 1)))
      = PowerSeries.C ((typeBFaceNumber n k : R)) * (X ^ k * (1 - X) ^ (n - k)) *
          ((1 - X) ^ (k + 1) * PowerSeries.mk 1 ^ (k + 1)) := by rw [hsplit]; ring
    _ = _ := by rw [hunit, mul_one]

end

end Fabius
