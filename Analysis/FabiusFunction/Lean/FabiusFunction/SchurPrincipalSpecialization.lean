import FabiusFunction.VandermondeAlternant
import FabiusFunction.FiniteQBinomialCore
import FabiusFunction.GeometricCompleteHomogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Principal specialization of a Schur bialternant

This module formalizes the monograph's `thm:schur-principal` and the two shadows of
`cor:schur-e-h` in the only form available inside Mathlib today: as identities between
**alternants**.

## Convention

Everything is indexed by `ℕ` and truncated to the first `m` places.  For an exponent
vector `mu : ℕ → ℕ` we set

`alternantPow q m mu = det (q ^ (i * mu j))_{i,j < m}`,

which is the monograph's `a_mu(1, q, ..., q^(m-1))` written with `0`-based indices.  The
staircase is `staircase m i = m - 1 - i` (the monograph's `delta`) and the exponent vector
attached to a partition `lam` is `schurExponent m lam i = lam i + (m - 1 - i)` (the
monograph's `mu_j = lam_j + m - j`).  The weight is `n(lam) = ∑_{j<m} j * lam j`.  The
monograph's hypothesis "`lam` is a partition with at most `m` parts" becomes the weakest
usable form `∀ i j, i < j → j < m → lam j ≤ lam i`.

## What IS covered

* `alternantPow_eq_prod`: the Vandermonde evaluation
  `a_mu = ∏_{i<j<m} (q ^ mu j - q ^ mu i)`, for an **arbitrary** exponent vector, over an
  arbitrary commutative ring and at an arbitrary `q`.  The source states this only for the
  `mu` attached to a partition.
* `alternantPow_eq_pow_mul_prod`: the monograph's factorisation
  `q^{mu_j} - q^{mu_i} = q^{mu_j}(1 - q^{mu_i - mu_j})` summed up, i.e.
  `a_mu = q ^ A(mu) * ∏_{i<j<m} (1 - q ^ (mu i - mu j))` with `A(mu) = ∑_j j * mu j`.
* `schur_principal_alternant`: **`thm:schur-principal` cleared of denominators**,
  `a_mu * ∏_{i<j}(1 - q^{j-i})
     = q^{n(lam)} * (∏_{i<j}(1 - q^{lam i - lam j + j - i})) * a_delta`,
  valid over every commutative ring and at every `q` — including `q = 0`, roots of unity,
  positive characteristic, rings with zero divisors, and the zero ring.  The source works in
  `ℚ(q)` only.
* `schur_principal_div` and `schur_principal_div_of_pow_ne_one`: the displayed quotient form
  in a field, under `a_delta ≠ 0`, respectively under the source's proviso `q ^ d ≠ 1` for
  `1 ≤ d < m` **together with `q ≠ 0`** (see the note on hypotheses below).
* `alternantPow_staircase_ne_zero`: the nonvanishing criterion for `a_delta`.
* `alternantPow_rowPartition`, `alternantPow_rowPartition_symm`: **`cor:schur-e-h` (ii)**, the
  one-row shadow, `a_{mu(k)} = [r+k, r]_q * a_delta = [r+k, k]_q * a_delta` with `m = r + 1`
  (the monograph's `[n+k-1, k]_q`).  Proved with **no** division, **no** cancellation, **no**
  hypothesis on `q` and **no** bound on `k` — strictly stronger than the source.
* `alternantPow_rowPartition_eq_completeHomogeneous`: the honest Lean form of the monograph's
  `s_{(k)} = h_k` at the principal specialization, closed against
  `Fabius.completeHomogeneousEval_geometric`.
* `qPochhammer_mul_alternantPow_columnPartition`: **`cor:schur-e-h` (i)** in cleared form,
  `(q;q)_k * a_{mu(1^k)} = q^{C(k,2)} * (q^{m-k+1};q)_k * a_delta`, over every commutative ring;
  and `alternantPow_columnPartition`, its cancelled form `q^{C(k,2)} [m,k]_q a_delta` in a field
  under `(q;q)_k ≠ 0`.

## What is NOT covered

* **There is no Schur polynomial.** Neither Mathlib nor this corpus defines `s_lam` (no
  bialternant API, no Jacobi–Trudi, no SSYT, no Pieri or Littlewood–Richardson rule).  The
  module therefore adopts the monograph's own bialternant *definition*
  (`def:schur-bialternant`) and states everything as a relation between `a_mu` and `a_delta`.
  Nothing here is a theorem about an independently defined `s_lam`.
* **The Macdonald citations `s_{(1^k)} = e_k` and `s_{(k)} = h_k` are not imported.** They need
  symmetric-function theory that does not exist here.  Only the row case's *specialization*
  consequence is closed (`alternantPow_rowPartition_eq_completeHomogeneous`); the column case's
  counterpart is unavailable because no principal specialization of `elementarySymmetricEval`
  exists in the corpus.  See the follow-up note below.
* **The divisibility clause of `lem:vandermonde-alternant`** (`a_delta ∣ a_mu` in
  `ℤ[x_1,...,x_m]`, hence `s_lam ∈ ℤ[x]`) is not proved; it needs a UFD argument in
  `MvPolynomial` and is not used by anything below.
* **The `q → 1` Weyl dimension formula** of `rem:schur-hypotheses` is not proved.
* The **unconditional** (arbitrary commutative ring, no `(q;q)_k ≠ 0`) form of
  `alternantPow_columnPartition`.  It is true — transport it from `Polynomial ℤ`, which is a
  domain — but the transport is left to a follow-up.

## A note on the hypotheses of the quotient form

The monograph reads the displayed quotient "at those `q` with `q^d ≠ 1` for `1 ≤ d ≤ m-1`".
That proviso is correct for the *polynomial* `s_lam`, but it does not by itself make the
*bialternant quotient* `a_mu / a_delta` meaningful: at `q = 0` with `m ≥ 3` every displayed
denominator is `1 - 0 = 1 ≠ 0`, while `a_delta(1, 0, ..., 0) = 0` because the specialization
point has repeated coordinates.  Since no independent `s_lam` is available, the Lean quotient
form must carry `a_delta ≠ 0`; `schur_principal_div_of_pow_ne_one` therefore adds `q ≠ 0`.

## Follow-up

`Fabius.elementarySymmetricEval (fun j : Fin N => q ^ j) k = q ^ C(k,2) * gaussianBinomial q N k`
is the missing half of `cor:schur-e-h`; it should be obtainable from
`Fabius.elementarySymmetricGeneratingSeries_eq_prod` together with
`Fabius.prod_one_add_mul_pow_eq_gaussianBinomial`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Matrix

/-! ### Index bridges

All later arguments live over `Finset.range` and `Finset.Ico`, where `omega` is available.
Only `alternantPow_eq_prod` ever meets a `Fin`-indexed double product, and it is converted
immediately by the following bridge. -/

/-- **Pair-index bridge.**  A `Fin`-indexed strict-upper-triangular double product equals the
corresponding `range`/`Ico`-indexed one. -/
theorem prod_Ioi_eq_prod_Ico {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ → ℕ → M) :
    ∏ i : Fin m, ∏ j ∈ Ioi i, f (i : ℕ) (j : ℕ)
      = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, f i j := by
  have hinner : ∀ i : Fin m,
      ∏ j ∈ Ioi i, f (i : ℕ) (j : ℕ) = ∏ j ∈ Ico ((i : ℕ) + 1) m, f (i : ℕ) j := by
    intro i
    have hmap : (Ioi i).map Fin.valEmbedding = Ico ((i : ℕ) + 1) m := by
      rw [Fin.map_valEmbedding_Ioi]
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    calc
      ∏ j ∈ Ioi i, f (i : ℕ) (j : ℕ)
          = ∏ j ∈ (Ioi i).map Fin.valEmbedding, f (i : ℕ) j :=
            (Finset.prod_map (Ioi i) Fin.valEmbedding fun j => f (i : ℕ) j).symm
      _ = ∏ j ∈ Ico ((i : ℕ) + 1) m, f (i : ℕ) j := by rw [hmap]
  calc
    ∏ i : Fin m, ∏ j ∈ Ioi i, f (i : ℕ) (j : ℕ)
        = ∏ i : Fin m, ∏ j ∈ Ico ((i : ℕ) + 1) m, f (i : ℕ) j :=
          Finset.prod_congr rfl fun i _ => hinner i
    _ = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, f i j :=
          Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Ico (i + 1) m, f i j) m

/-- The additive companion of the bridge: each `mu j` is counted once for every `i < j`,
so the strict-upper-triangular sum is the weighted sum `∑_j j * mu j`.  This is the
monograph's `A(mu) = ∑_{i<j} mu_j = ∑_j (j-1) mu_j`. -/
theorem sum_Ico_eq_sum_mul (m : ℕ) (mu : ℕ → ℕ) :
    ∑ i ∈ range m, ∑ j ∈ Ico (i + 1) m, mu j = ∑ j ∈ range m, j * mu j := by
  have hcomm : ∑ i ∈ range m, ∑ j ∈ Ico (i + 1) m, mu j
      = ∑ j ∈ range m, ∑ _i ∈ range j, mu j := by
    refine Finset.sum_comm' fun i j => ?_
    simp only [Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [hcomm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- Reindex a product over `Ico 1 (r+1)` as a product over `range r`. -/
private theorem prod_Ico_one_succ {M : Type*} [CommMonoid M] (r : ℕ) (g : ℕ → M) :
    ∏ j ∈ Ico 1 (r + 1), g j = ∏ d ∈ range r, g (1 + d) := by
  have h := Finset.prod_Ico_eq_prod_range g 1 (r + 1)
  rwa [Nat.add_sub_cancel] at h

/-- Split a product over `range m` at a cut point `k ≤ m`. -/
private theorem prod_range_split {M : Type*} [CommMonoid M] {m k : ℕ} (hk : k ≤ m)
    (g : ℕ → M) :
    (∏ i ∈ range k, g i) * ∏ i ∈ Ico k m, g i = ∏ i ∈ range m, g i := by
  simp only [Finset.range_eq_Ico]
  exact Finset.prod_Ico_consecutive g (Nat.zero_le k) hk

/-! ### The alternant at a geometric point -/

/-- The alternant `a_mu` of `def:schur-bialternant` evaluated at the principal
specialization `x_i = q^i`:  `a_mu(1, q, ..., q^(m-1)) = det (q ^ (i * mu j))_{i,j<m}`.

The exponent vector `mu : ℕ → ℕ` is completely arbitrary; only its first `m` values matter. -/
def alternantPow {R : Type*} [CommRing R] (q : R) (m : ℕ) (mu : ℕ → ℕ) : R :=
  (Matrix.of fun i j : Fin m => q ^ ((i : ℕ) * mu (j : ℕ))).det

/-- **Vandermonde evaluation of the alternant.**  Transposing turns the matrix
`(q^(i * mu_j))` into a Vandermonde matrix in the variables `y_j = q^(mu_j)`, so

`a_mu(1, q, ..., q^(m-1)) = ∏_{i<j<m} (q^(mu j) - q^(mu i))`.

No monotonicity or distinctness hypothesis on `mu` is needed, and the identity holds over
every commutative ring at every `q`. -/
theorem alternantPow_eq_prod {R : Type*} [CommRing R] (q : R) (m : ℕ) (mu : ℕ → ℕ) :
    alternantPow q m mu = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (q ^ mu j - q ^ mu i) := by
  have hmat : (Matrix.of fun i j : Fin m => q ^ ((i : ℕ) * mu (j : ℕ)))
      = (Matrix.vandermonde fun j : Fin m => q ^ mu (j : ℕ))ᵀ := by
    ext i j
    show q ^ ((i : ℕ) * mu (j : ℕ)) = (q ^ mu (j : ℕ)) ^ (i : ℕ)
    rw [← pow_mul, Nat.mul_comm]
  have h0 : alternantPow q m mu
      = ∏ i : Fin m, ∏ j ∈ Ioi i, (q ^ mu (j : ℕ) - q ^ mu (i : ℕ)) := by
    rw [alternantPow, hmat, Matrix.det_transpose]
    exact det_vandermonde_eq_prod (fun j : Fin m => q ^ mu (j : ℕ))
  rw [h0]
  exact prod_Ioi_eq_prod_Ico m fun i j => q ^ mu j - q ^ mu i

/-- **Factoring out the lower power.**  For a vector that is antitone on `[0, m)` the
monograph's step `q^{mu_j} - q^{mu_i} = q^{mu_j} (1 - q^{mu_i - mu_j})` gives

`a_mu = q ^ (∑_j j * mu j) * ∏_{i<j<m} (1 - q ^ (mu i - mu j))`.

Only the *smaller* power is extracted, so no sign appears. -/
theorem alternantPow_eq_pow_mul_prod {R : Type*} [CommRing R] (q : R) (m : ℕ) (mu : ℕ → ℕ)
    (hmu : ∀ i j, i < j → j < m → mu j ≤ mu i) :
    alternantPow q m mu
      = q ^ (∑ j ∈ range m, j * mu j) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (mu i - mu j)) := by
  rw [alternantPow_eq_prod]
  have hrow : ∀ i ∈ range m,
      (∏ j ∈ Ico (i + 1) m, (q ^ mu j - q ^ mu i))
        = q ^ (∑ j ∈ Ico (i + 1) m, mu j) *
          ∏ j ∈ Ico (i + 1) m, (1 - q ^ (mu i - mu j)) := by
    intro i _
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have hle : mu j ≤ mu i := hmu i j (by omega) hjm
    have hexp : mu j + (mu i - mu j) = mu i := by omega
    show q ^ mu j - q ^ mu i = q ^ mu j * (1 - q ^ (mu i - mu j))
    rw [mul_sub, mul_one, ← pow_add, hexp]
  have hstep : (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (q ^ mu j - q ^ mu i))
      = ∏ i ∈ range m, (q ^ (∑ j ∈ Ico (i + 1) m, mu j) *
          ∏ j ∈ Ico (i + 1) m, (1 - q ^ (mu i - mu j))) :=
    Finset.prod_congr rfl hrow
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_Ico_eq_sum_mul m mu]

/-! ### The staircase and the exponent vector of a partition -/

/-- The staircase `delta = (m-1, m-2, ..., 0)` of `def:schur-bialternant`, `0`-indexed. -/
def staircase (m i : ℕ) : ℕ := m - 1 - i

/-- The exponent vector `mu_j = lam_j + m - j` of `def:schur-bialternant`, `0`-indexed. -/
def schurExponent (m : ℕ) (lam : ℕ → ℕ) (i : ℕ) : ℕ := lam i + (m - 1 - i)

/-- The staircase evaluation `a_delta = q^{A(delta)} ∏_{i<j<m} (1 - q^{j-i})`. -/
theorem alternantPow_staircase {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    alternantPow q m (staircase m)
      = q ^ (∑ j ∈ range m, j * staircase m j) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
  have hmono : ∀ i j, i < j → j < m → staircase m j ≤ staircase m i := by
    intro i j hij hjm
    simp only [staircase]
    omega
  have hbody : (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
        (1 - q ^ (staircase m i - staircase m j)))
      = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have hexp : staircase m i - staircase m j = j - i := by
      simp only [staircase]
      omega
    rw [hexp]
  rw [alternantPow_eq_pow_mul_prod q m (staircase m) hmono, hbody]

/-- The partition evaluation
`a_mu = q^{n(lam) + A(delta)} ∏_{i<j<m} (1 - q^{lam i - lam j + j - i})`.
The weight is written additively as `A(mu) = n(lam) + A(delta)`, which avoids the truncated
subtraction `A(mu) - A(delta)` used in the source. -/
theorem alternantPow_schurExponent {R : Type*} [CommRing R] (q : R) (m : ℕ) (lam : ℕ → ℕ)
    (hlam : ∀ i j, i < j → j < m → lam j ≤ lam i) :
    alternantPow q m (schurExponent m lam)
      = q ^ ((∑ j ∈ range m, j * lam j) + ∑ j ∈ range m, j * staircase m j) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (lam i - lam j + (j - i))) := by
  have hmono : ∀ i j, i < j → j < m → schurExponent m lam j ≤ schurExponent m lam i := by
    intro i j hij hjm
    have hle := hlam i j hij hjm
    simp only [schurExponent]
    omega
  have hsum : (∑ j ∈ range m, j * schurExponent m lam j)
      = (∑ j ∈ range m, j * lam j) + ∑ j ∈ range m, j * staircase m j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [schurExponent, staircase]
    rw [mul_add]
  have hbody : (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
        (1 - q ^ (schurExponent m lam i - schurExponent m lam j)))
      = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (lam i - lam j + (j - i))) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have hle : lam j ≤ lam i := hlam i j (by omega) hjm
    have hexp : schurExponent m lam i - schurExponent m lam j = lam i - lam j + (j - i) := by
      simp only [schurExponent]
      omega
    rw [hexp]
  rw [alternantPow_eq_pow_mul_prod q m (schurExponent m lam) hmono, hsum, hbody]

/-! ### `thm:schur-principal` -/

/-- **Principal specialization of a Schur bialternant, cleared of denominators.**

This is `thm:schur-principal`:

`a_mu * ∏_{i<j<m} (1 - q^{j-i})
   = q^{n(lam)} * (∏_{i<j<m} (1 - q^{lam i - lam j + j - i})) * a_delta`,

where `mu = schurExponent m lam` and `n(lam) = ∑_j j * lam j`.  Dividing by
`a_delta = q^{A(delta)} ∏_{i<j}(1 - q^{j-i})` recovers the displayed quotient, but the
cleared statement needs no division: it holds over every commutative ring and at every `q`,
including `q = 0`, roots of unity, positive characteristic and rings with zero divisors.
The source proves it in `ℚ(q)`. -/
theorem schur_principal_alternant {R : Type*} [CommRing R] (q : R) (m : ℕ) (lam : ℕ → ℕ)
    (hlam : ∀ i j, i < j → j < m → lam j ≤ lam i) :
    alternantPow q m (schurExponent m lam) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i))
      = q ^ (∑ j ∈ range m, j * lam j) *
          (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (lam i - lam j + (j - i)))) *
          alternantPow q m (staircase m) := by
  have hpw : q ^ ((∑ j ∈ range m, j * lam j) + ∑ j ∈ range m, j * staircase m j)
      = q ^ (∑ j ∈ range m, j * lam j) * q ^ (∑ j ∈ range m, j * staircase m j) :=
    pow_add q _ _
  rw [alternantPow_schurExponent q m lam hlam, alternantPow_staircase q m, hpw]
  ring

/-- The staircase alternant is nonzero as soon as `q ≠ 0` and no `q^d = 1` for `0 < d < m`.
This is exactly the monograph's proviso together with the extra hypothesis `q ≠ 0` that the
bialternant quotient — as opposed to the polynomial `s_lam` — genuinely needs. -/
theorem alternantPow_staircase_ne_zero {K : Type*} [Field K] (q : K) (m : ℕ) (hq : q ≠ 0)
    (hroot : ∀ d, 0 < d → d < m → q ^ d ≠ 1) :
    alternantPow q m (staircase m) ≠ 0 := by
  rw [alternantPow_staircase]
  refine mul_ne_zero (pow_ne_zero _ hq) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
  have hne : q ^ (j - i) ≠ 1 := hroot (j - i) (by omega) (by omega)
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- **`thm:schur-principal` in the displayed quotient form**, in a field, under the
nonvanishing of the staircase alternant. -/
theorem schur_principal_div {K : Type*} [Field K] (q : K) (m : ℕ) (lam : ℕ → ℕ)
    (hlam : ∀ i j, i < j → j < m → lam j ≤ lam i)
    (hdelta : alternantPow q m (staircase m) ≠ 0) :
    alternantPow q m (schurExponent m lam) / alternantPow q m (staircase m)
      = q ^ (∑ j ∈ range m, j * lam j) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
          ((1 - q ^ (lam i - lam j + (j - i))) / (1 - q ^ (j - i))) := by
  have hPB : (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i))) ≠ 0 := by
    intro h
    apply hdelta
    rw [alternantPow_staircase, h, mul_zero]
  have hsplit : (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
        ((1 - q ^ (lam i - lam j + (j - i))) / (1 - q ^ (j - i))))
      = (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (lam i - lam j + (j - i)))) /
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_div_distrib _ _
  rw [hsplit, ← mul_div_assoc, div_eq_div_iff hdelta hPB]
  exact schur_principal_alternant q m lam hlam

/-- The quotient form under the monograph's literal proviso `q^d ≠ 1` for `1 ≤ d ≤ m-1`,
supplemented by `q ≠ 0`. -/
theorem schur_principal_div_of_pow_ne_one {K : Type*} [Field K] (q : K) (m : ℕ)
    (lam : ℕ → ℕ) (hlam : ∀ i j, i < j → j < m → lam j ≤ lam i) (hq : q ≠ 0)
    (hroot : ∀ d, 0 < d → d < m → q ^ d ≠ 1) :
    alternantPow q m (schurExponent m lam) / alternantPow q m (staircase m)
      = q ^ (∑ j ∈ range m, j * lam j) *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
          ((1 - q ^ (lam i - lam j + (j - i))) / (1 - q ^ (j - i))) :=
  schur_principal_div q m lam hlam (alternantPow_staircase_ne_zero q m hq hroot)

/-! ### `cor:schur-e-h` (ii): the one-row shadow -/

/-- The one-row partition `lam = (k)`. -/
def rowPartition (k i : ℕ) : ℕ := if i = 0 then k else 0

/-- The one-row partition is antitone. -/
theorem rowPartition_antitone (k i j : ℕ) (hij : i < j) :
    rowPartition k j ≤ rowPartition k i := by
  have hj : j ≠ 0 := by omega
  have h : rowPartition k j = 0 := by simp [rowPartition, hj]
  rw [h]
  exact Nat.zero_le _

/-- The one-row partition has weight `n(lam) = 0`. -/
theorem sum_mul_rowPartition (m k : ℕ) : ∑ j ∈ range m, j * rowPartition k j = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with hj | hj
  · rw [hj, Nat.zero_mul]
  · have hjne : j ≠ 0 := by omega
    have h : rowPartition k j = 0 := by simp [rowPartition, hjne]
    rw [h, Nat.mul_zero]

/-- **`cor:schur-e-h` (ii).**  With `m = r + 1` variables the one-row bialternant is the
Gaussian coefficient `[r+k, r]_q` times the staircase alternant:

`a_{mu((k))}(1, q, ..., q^r) = [r+k, r]_q * a_delta(1, q, ..., q^r)`.

The proof uses **no** cancellation: the `(q;q)_r` produced by
`finiteQPochhammerIn_self_mul_gaussianBinomial` is literally the `i = 0` row of `a_delta`.
Hence the identity holds over every commutative ring, at every `q`, and for every `k`. -/
theorem alternantPow_rowPartition {R : Type*} [CommRing R] (q : R) (r k : ℕ) :
    alternantPow q (r + 1) (schurExponent (r + 1) (rowPartition k))
      = gaussianBinomial q (r + k) r * alternantPow q (r + 1) (staircase (r + 1)) := by
  have hlam : ∀ i j, i < j → j < r + 1 → rowPartition k j ≤ rowPartition k i :=
    fun i j hij _ => rowPartition_antitone k i j hij
  -- split both double products at the row `i = 0`
  have hsplitmu :
      (∏ i ∈ range (r + 1), ∏ j ∈ Ico (i + 1) (r + 1),
          (1 - q ^ (rowPartition k i - rowPartition k j + (j - i))))
        = (∏ i ∈ range r, ∏ j ∈ Ico (i + 1 + 1) (r + 1),
            (1 - q ^ (rowPartition k (i + 1) - rowPartition k j + (j - (i + 1))))) *
          ∏ j ∈ Ico (0 + 1) (r + 1),
            (1 - q ^ (rowPartition k 0 - rowPartition k j + (j - 0))) :=
    Finset.prod_range_succ' (fun i => ∏ j ∈ Ico (i + 1) (r + 1),
      (1 - q ^ (rowPartition k i - rowPartition k j + (j - i)))) r
  have hsplitdel :
      (∏ i ∈ range (r + 1), ∏ j ∈ Ico (i + 1) (r + 1), (1 - q ^ (j - i)))
        = (∏ i ∈ range r, ∏ j ∈ Ico (i + 1 + 1) (r + 1), (1 - q ^ (j - (i + 1)))) *
          ∏ j ∈ Ico (0 + 1) (r + 1), (1 - q ^ (j - 0)) :=
    Finset.prod_range_succ' (fun i => ∏ j ∈ Ico (i + 1) (r + 1), (1 - q ^ (j - i))) r
  -- every row above `i = 0` is common to the two products
  have htail :
      (∏ i ∈ range r, ∏ j ∈ Ico (i + 1 + 1) (r + 1),
          (1 - q ^ (rowPartition k (i + 1) - rowPartition k j + (j - (i + 1)))))
        = ∏ i ∈ range r, ∏ j ∈ Ico (i + 1 + 1) (r + 1), (1 - q ^ (j - (i + 1))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have h1 : rowPartition k (i + 1) = 0 := by
      have hne : i + 1 ≠ 0 := by omega
      simp [rowPartition, hne]
    have h2 : rowPartition k j = 0 := by
      have hjne : j ≠ 0 := by omega
      simp [rowPartition, hjne]
    have hexp : rowPartition k (i + 1) - rowPartition k j + (j - (i + 1)) = j - (i + 1) := by
      omega
    rw [hexp]
  -- the `i = 0` rows are shifted q-Pochhammer products
  have hmu0 : (∏ j ∈ Ico (0 + 1) (r + 1),
        (1 - q ^ (rowPartition k 0 - rowPartition k j + (j - 0))))
      = finiteQPochhammerIn (q ^ (k + 1)) q r := by
    have hz : Ico (0 + 1) (r + 1) = Ico 1 (r + 1) := by rw [Nat.zero_add]
    rw [hz, prod_Ico_one_succ r
      (fun j => 1 - q ^ (rowPartition k 0 - rowPartition k j + (j - 0))),
      finiteQPochhammerIn]
    refine Finset.prod_congr rfl fun d _ => ?_
    have h1 : rowPartition k 0 = k := by simp [rowPartition]
    have h2 : rowPartition k (1 + d) = 0 := by
      have hne : 1 + d ≠ 0 := by omega
      simp [rowPartition, hne]
    have hexp : rowPartition k 0 - rowPartition k (1 + d) + (1 + d - 0) = k + 1 + d := by
      omega
    have hp : q ^ (k + 1 + d) = q ^ (k + 1) * q ^ d := pow_add q (k + 1) d
    show (1 : R) - q ^ (rowPartition k 0 - rowPartition k (1 + d) + (1 + d - 0))
        = 1 - q ^ (k + 1) * q ^ d
    rw [hexp, hp]
  have hdel0 : (∏ j ∈ Ico (0 + 1) (r + 1), (1 - q ^ (j - 0)))
      = finiteQPochhammerIn q q r := by
    have hz : Ico (0 + 1) (r + 1) = Ico 1 (r + 1) := by rw [Nat.zero_add]
    rw [hz, prod_Ico_one_succ r (fun j => 1 - q ^ (j - 0)), finiteQPochhammerIn]
    refine Finset.prod_congr rfl fun d _ => ?_
    have hexp : 1 + d - 0 = 1 + d := by omega
    have hp : q ^ (1 + d) = q * q ^ d := by rw [pow_add, pow_one]
    show (1 : R) - q ^ (1 + d - 0) = 1 - q * q ^ d
    rw [hexp, hp]
  have hpoch : finiteQPochhammerIn (q ^ (k + 1)) q r
      = finiteQPochhammerIn q q r * gaussianBinomial q (r + k) r := by
    have h := finiteQPochhammerIn_self_mul_gaussianBinomial q (show r ≤ r + k by omega)
    have hidx : r + k - r + 1 = k + 1 := by omega
    rw [hidx] at h
    exact h.symm
  have hkey : (∏ i ∈ range (r + 1), ∏ j ∈ Ico (i + 1) (r + 1),
        (1 - q ^ (rowPartition k i - rowPartition k j + (j - i))))
      = gaussianBinomial q (r + k) r *
        ∏ i ∈ range (r + 1), ∏ j ∈ Ico (i + 1) (r + 1), (1 - q ^ (j - i)) := by
    rw [hsplitmu, hsplitdel, htail, hmu0, hdel0, hpoch]
    ring
  have hz0 : q ^ (0 + ∑ j ∈ range (r + 1), j * staircase (r + 1) j)
      = q ^ (∑ j ∈ range (r + 1), j * staircase (r + 1) j) := by
    rw [Nat.zero_add]
  rw [alternantPow_schurExponent q (r + 1) (rowPartition k) hlam,
    alternantPow_staircase q (r + 1), sum_mul_rowPartition (r + 1) k, hz0, hkey]
  ring

/-- `cor:schur-e-h` (ii) in the monograph's index convention `[n+k-1, k]_q` with `n = r+1`. -/
theorem alternantPow_rowPartition_symm {R : Type*} [CommRing R] (q : R) (r k : ℕ) :
    alternantPow q (r + 1) (schurExponent (r + 1) (rowPartition k))
      = gaussianBinomial q (r + k) k * alternantPow q (r + 1) (staircase (r + 1)) := by
  rw [alternantPow_rowPartition, gaussianBinomial_add_symm q r k]

/-- The Lean form of the monograph's `s_{(k)} = h_k` **at the principal specialization**:
the one-row bialternant quotient is the complete homogeneous polynomial of degree `k`
evaluated at `(1, q, ..., q^r)`.  The general symmetric-function identity `s_{(k)} = h_k`
is a citation to Macdonald that cannot be imported here. -/
theorem alternantPow_rowPartition_eq_completeHomogeneous {R : Type*} [CommRing R] (q : R)
    (r k : ℕ) :
    alternantPow q (r + 1) (schurExponent (r + 1) (rowPartition k))
      = completeHomogeneousEval (fun j : Fin (r + 1) => q ^ (j : ℕ)) k *
        alternantPow q (r + 1) (staircase (r + 1)) := by
  rw [alternantPow_rowPartition, completeHomogeneousEval_geometric q k r, Nat.add_comm k r]

/-! ### `cor:schur-e-h` (i): the one-column shadow -/

/-- The one-column partition `lam = (1^k)`. -/
def columnPartition (k i : ℕ) : ℕ := if i < k then 1 else 0

/-- The one-column partition is antitone. -/
theorem columnPartition_antitone (k i j : ℕ) (hij : i < j) :
    columnPartition k j ≤ columnPartition k i := by
  simp only [columnPartition]
  split_ifs <;> omega

/-- The one-column partition has weight `n(lam) = C(k,2)`. -/
theorem sum_mul_columnPartition (m k : ℕ) (hk : k ≤ m) :
    ∑ j ∈ range m, j * columnPartition k j = k.choose 2 := by
  have hsub : range k ⊆ range m := Finset.range_subset_range.mpr hk
  have hzero : ∀ x ∈ range m, x ∉ range k → x * columnPartition k x = 0 := by
    intro x _ hx
    have hxk : ¬ x < k := fun hlt => hx (Finset.mem_range.mpr hlt)
    have h : columnPartition k x = 0 := by simp [columnPartition, hxk]
    rw [h, Nat.mul_zero]
  have h1 : (∑ j ∈ range k, j * columnPartition k j)
      = ∑ j ∈ range m, j * columnPartition k j := Finset.sum_subset hsub hzero
  have h2 : (∑ j ∈ range k, j * columnPartition k j) = ∑ j ∈ range k, j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have h : columnPartition k j = 1 := by simp [columnPartition, hjk]
    rw [h, Nat.mul_one]
  rw [← h1, h2, Finset.sum_range_id, Nat.choose_two_right]

/-- The telescoping step behind `cor:schur-e-h` (i).  Both sides equal
`∏_{d ≤ N} (1 - q^{c+d})`, read off from the two ways of peeling one factor. -/
private theorem prod_telescope_step {R : Type*} [CommRing R] (q : R) (c N : ℕ) :
    (1 - q ^ c) * ∏ d ∈ range N, (1 - q ^ (c + 1 + d))
      = (1 - q ^ (c + N)) * ∏ d ∈ range N, (1 - q ^ (c + d)) := by
  have h1 : (∏ d ∈ range (N + 1), (1 - q ^ (c + d)))
      = (∏ d ∈ range N, (1 - q ^ (c + (d + 1)))) * (1 - q ^ c) :=
    Finset.prod_range_succ' (fun d => 1 - q ^ (c + d)) N
  have h2 : (∏ d ∈ range (N + 1), (1 - q ^ (c + d)))
      = (∏ d ∈ range N, (1 - q ^ (c + d))) * (1 - q ^ (c + N)) :=
    Finset.prod_range_succ (fun d => 1 - q ^ (c + d)) N
  have h3 : (∏ d ∈ range N, (1 - q ^ (c + (d + 1))))
      = ∏ d ∈ range N, (1 - q ^ (c + 1 + d)) := by
    refine Finset.prod_congr rfl fun d _ => ?_
    have hd : c + (d + 1) = c + 1 + d := by omega
    rw [hd]
  have h4 : (∏ d ∈ range N, (1 - q ^ (c + 1 + d))) * (1 - q ^ c)
      = (∏ d ∈ range N, (1 - q ^ (c + d))) * (1 - q ^ (c + N)) := by
    rw [← h3, ← h1, h2]
  linear_combination h4

/-- One row `i < k` of the one-column comparison.  Multiplying the `mu`-row by
`1 - q^{k-i}` and the `delta`-row by `1 - q^{m-i}` makes the two rows agree; this is the
monograph's telescoping `∏_{j>k} (1-q^{j-i+1})/(1-q^{j-i}) = (1-q^{m-i})/(1-q^{k-i})`,
written without any division. -/
private theorem column_row_step {R : Type*} [CommRing R] (q : R) (m k i : ℕ) (hik : i < k)
    (hkm : k ≤ m) :
    (1 - q ^ (k - i)) *
        ∏ j ∈ Ico (i + 1) m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i)))
      = (1 - q ^ (m - i)) * ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
  have hsplitmu :
      (∏ j ∈ Ico (i + 1) k,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i)))) *
        (∏ j ∈ Ico k m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
        = ∏ j ∈ Ico (i + 1) m,
            (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))) :=
    Finset.prod_Ico_consecutive
      (fun j => 1 - q ^ (columnPartition k i - columnPartition k j + (j - i)))
      (by omega) hkm
  have hsplitdel :
      (∏ j ∈ Ico (i + 1) k, (1 - q ^ (j - i))) * (∏ j ∈ Ico k m, (1 - q ^ (j - i)))
        = ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) :=
    Finset.prod_Ico_consecutive (fun j => 1 - q ^ (j - i)) (by omega) hkm
  have hlow : (∏ j ∈ Ico (i + 1) k,
        (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
      = ∏ j ∈ Ico (i + 1) k, (1 - q ^ (j - i)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjk⟩ := Finset.mem_Ico.mp hj
    have h1 : columnPartition k i = 1 := by simp [columnPartition, hik]
    have h2 : columnPartition k j = 1 := by simp [columnPartition, hjk]
    have hexp : columnPartition k i - columnPartition k j + (j - i) = j - i := by omega
    rw [hexp]
  have hhigh : (1 - q ^ (k - i)) *
        ∏ j ∈ Ico k m, (1 - q ^ (columnPartition k i - columnPartition k j + (j - i)))
      = (1 - q ^ (m - i)) * ∏ j ∈ Ico k m, (1 - q ^ (j - i)) := by
    have hmuhigh : (∏ j ∈ Ico k m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
        = ∏ d ∈ range (m - k), (1 - q ^ (k - i + 1 + d)) := by
      rw [Finset.prod_Ico_eq_prod_range
        (fun j => 1 - q ^ (columnPartition k i - columnPartition k j + (j - i))) k m]
      refine Finset.prod_congr rfl fun d hd => ?_
      have hd' : d < m - k := Finset.mem_range.mp hd
      have h1 : columnPartition k i = 1 := by simp [columnPartition, hik]
      have h2 : columnPartition k (k + d) = 0 := by
        have hkd : ¬ (k + d < k) := by omega
        simp [columnPartition, hkd]
      have hexp : columnPartition k i - columnPartition k (k + d) + (k + d - i)
          = k - i + 1 + d := by omega
      show (1 : R) - q ^ (columnPartition k i - columnPartition k (k + d) + (k + d - i))
          = 1 - q ^ (k - i + 1 + d)
      rw [hexp]
    have hdelhigh : (∏ j ∈ Ico k m, (1 - q ^ (j - i)))
        = ∏ d ∈ range (m - k), (1 - q ^ (k - i + d)) := by
      rw [Finset.prod_Ico_eq_prod_range (fun j => 1 - q ^ (j - i)) k m]
      refine Finset.prod_congr rfl fun d hd => ?_
      have hd' : d < m - k := Finset.mem_range.mp hd
      have hexp : k + d - i = k - i + d := by omega
      show (1 : R) - q ^ (k + d - i) = 1 - q ^ (k - i + d)
      rw [hexp]
    have hmi : m - i = k - i + (m - k) := by omega
    rw [hmuhigh, hdelhigh, hmi]
    exact prod_telescope_step q (k - i) (m - k)
  rw [← hsplitmu, ← hsplitdel, hlow]
  linear_combination (∏ j ∈ Ico (i + 1) k, (1 - q ^ (j - i))) * hhigh

/-- **`cor:schur-e-h` (i), cleared of denominators.**  For `k ≤ m`,

`(q;q)_k * a_{mu((1^k))} = q^{C(k,2)} * (q^{m-k+1};q)_k * a_delta`.

No division and no cancellation occur, so the identity holds over every commutative ring
and at every `q`. -/
theorem qPochhammer_mul_alternantPow_columnPartition {R : Type*} [CommRing R] (q : R)
    (m k : ℕ) (hk : k ≤ m) :
    finiteQPochhammerIn q q k * alternantPow q m (schurExponent m (columnPartition k))
      = q ^ k.choose 2 * finiteQPochhammerIn (q ^ (m - k + 1)) q k *
        alternantPow q m (staircase m) := by
  have hlam : ∀ i j, i < j → j < m → columnPartition k j ≤ columnPartition k i :=
    fun i j hij _ => columnPartition_antitone k i j hij
  have hsplitmu :
      (∏ i ∈ range k, ∏ j ∈ Ico (i + 1) m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i)))) *
        (∏ i ∈ Ico k m, ∏ j ∈ Ico (i + 1) m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
        = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
            (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))) :=
    prod_range_split hk (fun i => ∏ j ∈ Ico (i + 1) m,
      (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
  have hsplitdel :
      (∏ i ∈ range k, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i))) *
        (∏ i ∈ Ico k m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)))
        = ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) :=
    prod_range_split hk (fun i => ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)))
  have htop : (∏ i ∈ Ico k m, ∏ j ∈ Ico (i + 1) m,
        (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
      = ∏ i ∈ Ico k m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨hki, him⟩ := Finset.mem_Ico.mp hi
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have h1 : columnPartition k i = 0 := by
      have hki' : ¬ (i < k) := by omega
      simp [columnPartition, hki']
    have h2 : columnPartition k j = 0 := by
      have hkj' : ¬ (j < k) := by omega
      simp [columnPartition, hkj']
    have hexp : columnPartition k i - columnPartition k j + (j - i) = j - i := by omega
    rw [hexp]
  have hbot : (∏ i ∈ range k, (1 - q ^ (k - i))) *
        (∏ i ∈ range k, ∏ j ∈ Ico (i + 1) m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
      = (∏ i ∈ range k, (1 - q ^ (m - i))) *
        ∏ i ∈ range k, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    exact column_row_step q m k i (Finset.mem_range.mp hi) hk
  have hpochk : (∏ i ∈ range k, (1 - q ^ (k - i))) = finiteQPochhammerIn q q k := by
    rw [finiteQPochhammerIn, ← Finset.prod_range_reflect (fun i => 1 - q ^ (k - i)) k]
    refine Finset.prod_congr rfl fun d hd => ?_
    have hd' : d < k := Finset.mem_range.mp hd
    have hexp : k - (k - 1 - d) = 1 + d := by omega
    have hp : q ^ (1 + d) = q * q ^ d := by rw [pow_add, pow_one]
    show (1 : R) - q ^ (k - (k - 1 - d)) = 1 - q * q ^ d
    rw [hexp, hp]
  have hpochm : (∏ i ∈ range k, (1 - q ^ (m - i)))
      = finiteQPochhammerIn (q ^ (m - k + 1)) q k := by
    rw [finiteQPochhammerIn, ← Finset.prod_range_reflect (fun i => 1 - q ^ (m - i)) k]
    refine Finset.prod_congr rfl fun d hd => ?_
    have hd' : d < k := Finset.mem_range.mp hd
    have hexp : m - (k - 1 - d) = m - k + 1 + d := by omega
    have hp : q ^ (m - k + 1 + d) = q ^ (m - k + 1) * q ^ d := pow_add q (m - k + 1) d
    show (1 : R) - q ^ (m - (k - 1 - d)) = 1 - q ^ (m - k + 1) * q ^ d
    rw [hexp, hp]
  have hkey : finiteQPochhammerIn q q k *
        (∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m,
          (1 - q ^ (columnPartition k i - columnPartition k j + (j - i))))
      = finiteQPochhammerIn (q ^ (m - k + 1)) q k *
        ∏ i ∈ range m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i)) := by
    rw [← hpochk, ← hpochm, ← hsplitmu, ← hsplitdel, htop]
    linear_combination
      (∏ i ∈ Ico k m, ∏ j ∈ Ico (i + 1) m, (1 - q ^ (j - i))) * hbot
  have hpw : q ^ (k.choose 2 + ∑ j ∈ range m, j * staircase m j)
      = q ^ k.choose 2 * q ^ (∑ j ∈ range m, j * staircase m j) := pow_add q _ _
  rw [alternantPow_schurExponent q m (columnPartition k) hlam, alternantPow_staircase q m,
    sum_mul_columnPartition m k hk, hpw]
  linear_combination
    (q ^ k.choose 2 * q ^ (∑ j ∈ range m, j * staircase m j)) * hkey

/-- **`cor:schur-e-h` (i), cancelled.**  In a field, whenever `(q;q)_k ≠ 0`,

`a_{mu((1^k))} = q^{C(k,2)} * [m, k]_q * a_delta`,

which is the monograph's `s_{(1^k)}(1, q, ..., q^{n-1}) = q^{C(k,2)} [n, k]_q` read through
the bialternant.  The identification `s_{(1^k)} = e_k` is a Macdonald citation and is not
formalized. -/
theorem alternantPow_columnPartition {K : Type*} [Field K] (q : K) (m k : ℕ) (hk : k ≤ m)
    (hne : finiteQPochhammerIn q q k ≠ 0) :
    alternantPow q m (schurExponent m (columnPartition k))
      = q ^ k.choose 2 * gaussianBinomial q m k * alternantPow q m (staircase m) := by
  refine mul_left_cancel₀ hne ?_
  rw [qPochhammer_mul_alternantPow_columnPartition q m k hk]
  have hg := finiteQPochhammerIn_self_mul_gaussianBinomial q hk
  linear_combination (-(q ^ k.choose 2 * alternantPow q m (staircase m))) * hg

end Fabius
