import FabiusFunction.NarayanaNumbers

/-!
# Kirkman–Cayley dissection numbers and the associahedron face and `h` vectors

This module formalizes three statements of the combinatorial coefficient-calculus manuscript:
`thm:merged-kirkman-cayley` (the Kirkman–Cayley dissection formula), `cor:merged-associahedron-f`
(the associahedral face vector) and `thm:merged-associahedron-h` (the associahedral
`h`-polynomial).

## What is defined, and in which ring

The manuscript writes the dissection count as the *fraction*

`D(N,d) = (1/(d+1)) C(N+d-1, d) C(N-3, d)`.

Formalizing a definition with a division forces a choice.  Rather than divide in `ℚ`, or divide
in `ℕ` and carry the exactness of the division as a side condition, the count is **defined here
by a division-free `2×2` determinant of binomial coefficients in `ℤ`**,

`D(N,d) = C(N-3,d) C(N+d-1,d+1) - C(N-2,d+1) C(N+d-1,d)`      (`dissectionNumber`, in the
shifted variable `a = N - 3`),

exactly as `Fabius.narayana` is defined in `FabiusFunction.NarayanaNumbers`.  This keeps the
definition unconditional and the arithmetic in a ring, and it *makes* the integrality of the
manuscript's fraction a theorem rather than an assumption:

* `dissectionNumber_mul` is the manuscript formula in division-free shape,
  `(d+1) D(N,d) = C(N+d-1,d) C(N-3,d)`;
* `succ_dvd_choose_mul_choose` is the divisibility `(d+1) ∣ C(N+d-1,d) C(N-3,d)` that the
  division-free shape yields, and `dissectionNumber_eq_div` then identifies `dissectionNumber`
  with the manuscript's literal quotient `C(N+d-1,d) C(N-3,d) / (d+1)` taken in `ℕ`;
* `dissectionNumber_nonneg` records that the determinant is nonnegative, as a count must be.

The proof of `dissectionNumber_mul` is the whole content of the integrality: the two
elementary absorption identities `(d+1) C(a+1,d+1) = (a+1) C(a,d)` and
`(d+1) C(a+d+2,d+1) = (a+2) C(a+d+2,d)` turn the determinant into
`C(a,d) C(a+d+2,d) ((a+2) - (a+1))`.

Throughout, `N` is shifted to `a = N - 3` (dissections of a convex `N`-gon, `N ≥ 3`) or to the
pair `(j, e)` with `N = j + e + 3` (the `j`-faces, `e = N - 3 - j` being the number of diagonals
fixed), so that no truncated subtraction occurs inside a definition.  The manuscript-shaped
restatements with an explicit `N` and hypothesis `3 ≤ N` are
`dissectionNumber_mul_of_three_le` and `succ_dvd_choose_mul_choose_of_three_le`.

## What is deliberately NOT formalized

* **All bijective content.** The corpus does not construct polygon dissections, plane trees or
  the associahedron, and this module does not define them either.  In particular the statement
  that a `j`-face of the associahedron `Assoc_{N-3}` corresponds to a set of `N-3-j` pairwise
  noncrossing diagonals (the first half of `cor:merged-associahedron-f`), the cycle-lemma proof
  of `thm:merged-kirkman-cayley`, and the reading of `D(N,d)` as a count at all, are not
  formalizable here.  What is formalized is the *arithmetic* of the resulting numbers.
  Accordingly `associahedronFaceNumber` is **defined** as `D(N, N-3-j)`, which is the
  manuscript's conclusion, not derived from a face lattice.
* **The face transform `h(t) = ∑_d f_d (t-1)^d`.**  The manuscript derives the `h`-vector from
  the `f`-vector by that transform together with the alternating Vandermonde identity
  `∑_j (-1)^j C(M,j) C(R-j,S) = C(R-M,S-M)` (`eq:merged-alternating-vandermonde`).  Neither the
  transform nor that identity is proved here; `associahedronH` is instead **defined** as the
  Narayana number `N(N-2, r+1)`, which is the manuscript's conclusion, and the assertions of
  `thm:merged-associahedron-h` that are proved are the ones about that Narayana row: its closed
  form, its palindromicity, and `h(1) = C_{N-2}`.  The one consistency check between the two
  vectors that is proved is `associahedronHPoly_one_eq_faceNumber_zero`: `h(1) = f_0`.

## Main results

* `dissectionNumber`, `dissectionNumber_mul`, `succ_dvd_choose_mul_choose`,
  `dissectionNumber_eq_div`, `dissectionNumber_nonneg`, `dissectionNumber_eq_zero_of_lt`,
  `dissectionNumber_mul_of_three_le`, `succ_dvd_choose_mul_choose_of_three_le`
  (`thm:merged-kirkman-cayley`).
* `dissectionNumber_zero_right`, `dissectionNumber_one`, `dissectionNumber_self`.
* `associahedronFaceNumber`, `associahedronFaceNumber_eq`, `associahedronFaceNumber_mul`,
  `associahedronFaceNumber_zero`, `two_mul_associahedronFaceNumber_facet`,
  `associahedronFaceNumber_top` (`cor:merged-associahedron-f`).
* `associahedronH`, `associahedronH_eq`, `associahedronH_mul`, `associahedronH_symm`,
  `associahedronH_zero`, `associahedronH_top`, `sum_associahedronH`, `associahedronHPoly`,
  `associahedronHPoly_one`, `associahedronHPoly_one_eq_faceNumber_zero`
  (`thm:merged-associahedron-h`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The Kirkman–Cayley dissection numbers -/

/-- The Kirkman–Cayley number `D(N,d)` of sets of `d` pairwise noncrossing diagonals of a convex
`N`-gon, written in the shifted variable `a = N - 3` and **defined by the division-free
determinant**

`D(a+3, d) = C(a,d) C(a+d+2,d+1) - C(a+1,d+1) C(a+d+2,d)`.

The manuscript's fraction `(1/(d+1)) C(N+d-1,d) C(N-3,d)` is recovered in
`dissectionNumber_mul` and `dissectionNumber_eq_div`.  Nothing here constructs a dissection;
see the module docstring. -/
def dissectionNumber (a d : ℕ) : ℤ :=
  (a.choose d : ℤ) * ((a + d + 2).choose (d + 1) : ℤ) -
    ((a + 1).choose (d + 1) : ℤ) * ((a + d + 2).choose d : ℤ)

/-- **The Kirkman–Cayley dissection formula, division-free**
(`thm:merged-kirkman-cayley`, with `a = N - 3`):
`(d+1) D(N,d) = C(N+d-1,d) C(N-3,d)`. -/
theorem dissectionNumber_mul (a d : ℕ) :
    ((d : ℤ) + 1) * dissectionNumber a d =
      ((a + d + 2).choose d : ℤ) * (a.choose d : ℤ) := by
  have H1 : ((d : ℤ) + 1) * ((a + 1).choose (d + 1) : ℤ) = ((a : ℤ) + 1) * (a.choose d : ℤ) := by
    have h : (a + 1) * a.choose d = (a + 1).choose (d + 1) * (d + 1) := Nat.add_one_mul_choose_eq a d
    have hc := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at hc
    linarith [hc]
  have H2 : ((d : ℤ) + 1) * ((a + d + 2).choose (d + 1) : ℤ)
      = ((a + d + 2).choose d : ℤ) * ((a : ℤ) + 2) := by
    have h : (a + d + 2).choose (d + 1) * (d + 1) = (a + d + 2).choose d * (a + 2) := by
      have h0 := Nat.choose_succ_right_eq (a + d + 2) d
      rwa [show a + d + 2 - d = a + 2 from by omega] at h0
    have hc := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at hc
    linarith [hc]
  unfold dissectionNumber
  have expand : ((d : ℤ) + 1) *
      ((a.choose d : ℤ) * ((a + d + 2).choose (d + 1) : ℤ) -
        ((a + 1).choose (d + 1) : ℤ) * ((a + d + 2).choose d : ℤ))
      = (a.choose d : ℤ) * (((d : ℤ) + 1) * ((a + d + 2).choose (d + 1) : ℤ))
        - (((d : ℤ) + 1) * ((a + 1).choose (d + 1) : ℤ)) * ((a + d + 2).choose d : ℤ) := by
    ring
  rw [expand, H1, H2]
  ring

/-- **Integrality of the Kirkman–Cayley fraction:** `(d+1)` divides `C(N+d-1,d) C(N-3,d)`,
here with `a = N - 3`.  This is what makes the manuscript's `(1/(d+1)) C(N+d-1,d) C(N-3,d)` an
integer; it follows from the division-free form `dissectionNumber_mul`. -/
theorem succ_dvd_choose_mul_choose (a d : ℕ) :
    (d + 1) ∣ (a + d + 2).choose d * a.choose d := by
  have h : ((d + 1 : ℕ) : ℤ) ∣ (((a + d + 2).choose d * a.choose d : ℕ) : ℤ) := by
    refine ⟨dissectionNumber a d, ?_⟩
    push_cast
    exact (dissectionNumber_mul a d).symm
  exact_mod_cast h

/-- The determinant agrees with the manuscript's literal quotient, the division being taken in
`ℕ` and being exact by `succ_dvd_choose_mul_choose`. -/
theorem dissectionNumber_eq_div (a d : ℕ) :
    dissectionNumber a d = ((a + d + 2).choose d * a.choose d / (d + 1) : ℕ) := by
  have hne : ((d : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [dissectionNumber_mul]
  have hq : (d + 1) * ((a + d + 2).choose d * a.choose d / (d + 1))
      = (a + d + 2).choose d * a.choose d :=
    Nat.mul_div_cancel' (succ_dvd_choose_mul_choose a d)
  exact_mod_cast hq.symm

/-- The dissection numbers are nonnegative, as a count must be. -/
theorem dissectionNumber_nonneg (a d : ℕ) : 0 ≤ dissectionNumber a d := by
  have hpos : (0 : ℤ) < (d : ℤ) + 1 := by positivity
  have hprod : ((d : ℤ) + 1) * 0 ≤ ((d : ℤ) + 1) * dissectionNumber a d := by
    rw [mul_zero, dissectionNumber_mul]
    positivity
  exact le_of_mul_le_mul_left hprod hpos

/-- Outside the manuscript's range `0 ≤ d ≤ N - 3` the determinant vanishes: an `N`-gon has no
`d` pairwise noncrossing diagonals once `d > N - 3`. -/
theorem dissectionNumber_eq_zero_of_lt (a d : ℕ) (h : a < d) : dissectionNumber a d = 0 := by
  unfold dissectionNumber
  rw [Nat.choose_eq_zero_of_lt h,
    Nat.choose_eq_zero_of_lt (show a + 1 < d + 1 from by omega)]
  push_cast
  ring

/-- **The Kirkman–Cayley formula in the manuscript's variable** (`thm:merged-kirkman-cayley`):
for `N ≥ 3`, `(d+1) D(N,d) = C(N+d-1,d) C(N-3,d)`. -/
theorem dissectionNumber_mul_of_three_le (N d : ℕ) (hN : 3 ≤ N) :
    ((d : ℤ) + 1) * dissectionNumber (N - 3) d =
      ((N + d - 1).choose d : ℤ) * ((N - 3).choose d : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 3 := ⟨N - 3, by omega⟩
  rw [show a + 3 - 3 = a from by omega, show a + 3 + d - 1 = a + d + 2 from by omega]
  exact dissectionNumber_mul a d

/-- **Integrality in the manuscript's variable:** for `N ≥ 3`, `(d+1) ∣ C(N+d-1,d) C(N-3,d)`. -/
theorem succ_dvd_choose_mul_choose_of_three_le (N d : ℕ) (hN : 3 ≤ N) :
    (d + 1) ∣ (N + d - 1).choose d * (N - 3).choose d := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 3 := ⟨N - 3, by omega⟩
  rw [show a + 3 - 3 = a from by omega, show a + 3 + d - 1 = a + d + 2 from by omega]
  exact succ_dvd_choose_mul_choose a d

/-- `D(N,0) = 1`: the empty set of diagonals. -/
theorem dissectionNumber_zero_right (a : ℕ) : dissectionNumber a 0 = 1 := by
  unfold dissectionNumber
  rw [show a + 0 + 2 = a + 2 from by omega, show (0 : ℕ) + 1 = 1 from by omega,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_one_right, Nat.choose_zero_right]
  push_cast
  ring

/-- `2 D(N,1) = N (N-3)`: with `a = N - 3`, the `N`-gon has `N(N-3)/2` diagonals. -/
theorem dissectionNumber_one (a : ℕ) :
    2 * dissectionNumber a 1 = ((a : ℤ) + 3) * (a : ℤ) := by
  have h := dissectionNumber_mul a 1
  rw [show a + 1 + 2 = a + 3 from by omega, Nat.choose_one_right, Nat.choose_one_right] at h
  push_cast at h
  linarith [h]

/-- `D(N, N-3) = C_{N-2}`: the triangulations of a convex `N`-gon are counted by a Catalan
number.  Proved from `Fabius.succ_mul_catalan_succ`. -/
theorem dissectionNumber_self (a : ℕ) : dissectionNumber a a = catalan (a + 1) := by
  have hne : ((a : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [dissectionNumber_mul a a, Nat.choose_self, show a + a + 2 = 2 * a + 2 from by omega]
  have hc := congrArg (fun t : ℕ => (t : ℤ)) (succ_mul_catalan_succ a)
  push_cast at hc
  push_cast
  linarith [hc]

/-! ### The associahedral face vector -/

/-- The face number `f_j(Assoc_{N-3})`, **defined** as the Kirkman–Cayley number `D(N, N-3-j)`.

The manuscript's bijective step — that a `j`-face of the associahedron corresponds to a set of
`N-3-j` fixed pairwise noncrossing diagonals (`cor:merged-associahedron-f`) — is not formalized;
it is built into this definition.  What is proved below is the arithmetic of the resulting
numbers. -/
def associahedronFaceNumber (N j : ℕ) : ℤ := dissectionNumber (N - 3) (N - 3 - j)

/-- With `N = j + e + 3`, so that `e = N - 3 - j` is the number of fixed diagonals,
`f_j = D(N, e)`. -/
theorem associahedronFaceNumber_eq (j e : ℕ) :
    associahedronFaceNumber (j + e + 3) j = dissectionNumber (j + e) e := by
  have h1 : j + e + 3 - 3 = j + e := by omega
  have h2 : j + e - j = e := by omega
  simp only [associahedronFaceNumber, h1, h2]

/-- **The associahedral face vector** (`cor:merged-associahedron-f`), division-free: with
`N = j + e + 3`, so that `N - 2 - j = e + 1`, `2N - 4 - j = j + 2e + 2` and `N - 3 - j = e`,

`(N-2-j) f_j = C(2N-4-j, N-3-j) C(N-3, j)`. -/
theorem associahedronFaceNumber_mul (j e : ℕ) :
    ((e : ℤ) + 1) * associahedronFaceNumber (j + e + 3) j =
      ((j + 2 * e + 2).choose e : ℤ) * ((j + e).choose j : ℤ) := by
  have hsym : (j + e).choose e = (j + e).choose j := by
    have h : (j + e).choose ((j + e) - j) = (j + e).choose j := Nat.choose_symm (by omega)
    rwa [show (j + e) - j = e from by omega] at h
  rw [associahedronFaceNumber_eq, dissectionNumber_mul,
    show j + e + e + 2 = j + 2 * e + 2 from by omega, hsym]

/-- `f_0 = C_{N-2}`: the vertices of `Assoc_{N-3}` are the triangulations of the `N`-gon
(`cor:merged-associahedron-f`).  Here `N = m + 3`. -/
theorem associahedronFaceNumber_zero (m : ℕ) :
    associahedronFaceNumber (m + 3) 0 = catalan (m + 1) := by
  have h1 : m + 3 - 3 = m := by omega
  have h2 : m - 0 = m := by omega
  simp only [associahedronFaceNumber, h1, h2]
  exact dissectionNumber_self m

/-- `2 f_{N-4} = N (N-3)`: the facets of `Assoc_{N-3}` are the diagonals of the `N`-gon
(`cor:merged-associahedron-f`).  Here `N = j + 4`, so `N - 3 = j + 1`. -/
theorem two_mul_associahedronFaceNumber_facet (j : ℕ) :
    2 * associahedronFaceNumber (j + 4) j = ((j : ℤ) + 4) * ((j : ℤ) + 1) := by
  have h1 : j + 4 - 3 = j + 1 := by omega
  have h2 : j + 1 - j = 1 := by omega
  simp only [associahedronFaceNumber, h1, h2]
  have h := dissectionNumber_one (j + 1)
  push_cast at h
  linarith [h]

/-- `f_{N-3} = 1`: the unique top-dimensional face (`cor:merged-associahedron-f`).
Here `N = j + 3`. -/
theorem associahedronFaceNumber_top (j : ℕ) : associahedronFaceNumber (j + 3) j = 1 := by
  have h1 : j + 3 - 3 = j := by omega
  have h2 : j - j = 0 := by omega
  simp only [associahedronFaceNumber, h1, h2]
  exact dissectionNumber_zero_right j

/-! ### The associahedral `h`-polynomial -/

/-- The `h`-vector entry `h_r` of `Assoc_{N-3}`, **defined** as the Narayana number
`N(N-2, r+1)` of `FabiusFunction.NarayanaNumbers`.

The manuscript derives this from the face vector by the face transform
`h(t) = ∑_d f_d (t-1)^d` and the alternating Vandermonde identity; that derivation is not
formalized (see the module docstring), so the identification is taken as the definition and the
Narayana-row assertions of `thm:merged-associahedron-h` are what is proved. -/
def associahedronH (N r : ℕ) : ℤ := narayana (N - 2) (r + 1)

/-- With `N = m + 3`, the `h`-vector is the `(m+1)`st Narayana row. -/
theorem associahedronH_eq (m r : ℕ) : associahedronH (m + 3) r = narayana (m + 1) (r + 1) := by
  have h : m + 3 - 2 = m + 1 := by omega
  simp only [associahedronH, h]

/-- **The `h`-vector closed form** (`thm:merged-associahedron-h`), division-free: with
`N = m + 3`, `(N-2) h_r = C(N-2, r+1) C(N-2, r)`.  This is `Fabius.narayana_mul`. -/
theorem associahedronH_mul (m r : ℕ) :
    ((m : ℤ) + 1) * associahedronH (m + 3) r =
      ((m + 1).choose (r + 1) : ℤ) * ((m + 1).choose r : ℤ) := by
  rw [associahedronH_eq]
  exact narayana_mul m r

/-- **Palindromicity of the `h`-vector** (`thm:merged-associahedron-h`, the Dehn–Sommerville
relation for this polytope): with `N = m + 3` and `r ≤ m`, `h_r = h_{m-r}`, the indices running
over `0 ≤ r ≤ N - 3 = m`.  This is the Narayana symmetry `Fabius.narayana_symm`. -/
theorem associahedronH_symm (m r : ℕ) (hr : r ≤ m) :
    associahedronH (m + 3) r = associahedronH (m + 3) (m - r) := by
  rw [associahedronH_eq, associahedronH_eq]
  exact narayana_symm m r hr

/-- `h_0 = 1`. -/
theorem associahedronH_zero (m : ℕ) : associahedronH (m + 3) 0 = 1 := by
  rw [associahedronH_eq, narayana_succ_succ m 0]
  simp only [Nat.zero_add, Nat.choose_one_right, Nat.choose_zero_right]
  push_cast
  ring

/-- `h_{N-3} = 1`, by palindromicity. -/
theorem associahedronH_top (m : ℕ) : associahedronH (m + 3) m = 1 := by
  have h := associahedronH_symm m 0 (Nat.zero_le m)
  rw [Nat.sub_zero] at h
  rw [← h]
  exact associahedronH_zero m

/-- **The `h`-vector sums to a Catalan number** (`thm:merged-associahedron-h`):
`∑_{r=0}^{N-3} h_r = C_{N-2}`, with `N = m + 3`.  This is `Fabius.sum_narayana`. -/
theorem sum_associahedronH (m : ℕ) :
    ∑ r ∈ range (m + 1), associahedronH (m + 3) r = catalan (m + 1) := by
  rw [Finset.sum_congr rfl fun r _ => associahedronH_eq m r]
  exact sum_narayana m

/-- The associahedral `h`-polynomial `h(t) = ∑_{r=0}^{N-3} h_r t^r`, evaluated at `t`. -/
def associahedronHPoly (N : ℕ) (t : ℤ) : ℤ := ∑ r ∈ range (N - 2), associahedronH N r * t ^ r

/-- **`h(1) = C_{N-2}`** (`thm:merged-associahedron-h`), with `N = m + 3`. -/
theorem associahedronHPoly_one (m : ℕ) : associahedronHPoly (m + 3) 1 = catalan (m + 1) := by
  have h : m + 3 - 2 = m + 1 := by omega
  simp only [associahedronHPoly, h, one_pow, mul_one]
  exact sum_associahedronH m

/-- `h(1) = f_0`, the only consistency check between the face vector and the `h`-vector proved
here: both are `C_{N-2}`, as they must be for a simple polytope. -/
theorem associahedronHPoly_one_eq_faceNumber_zero (m : ℕ) :
    associahedronHPoly (m + 3) 1 = associahedronFaceNumber (m + 3) 0 := by
  rw [associahedronHPoly_one, associahedronFaceNumber_zero]

end Fabius
