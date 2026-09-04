import FabiusFunction.BoxPartitions
import FabiusFunction.GaussianBinomialPalindromic
import FabiusFunction.PartitionStabilization
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Symmetry and partial unimodality of the Gaussian coefficients

Write `[n,k]_q = c_0 + c_1 q + ⋯ + c_D q^D` with `D = k(n-k)`.  The printed theorem
`thm:qbinom-unimodal` of the `q`-Pochhammer / `q`-binomial monograph asserts two things:

* **symmetry** `c_j = c_{D-j}`, and
* **unimodality** `c_0 ≤ c_1 ≤ ⋯ ≤ c_{⌊D/2⌋}`.

Everything here is organised around the *box model*.  Setting `n = m + k`, the coefficient `c_j`
counts the partitions of `j` fitting inside a `k × m` rectangle,

`boxCoeff k m j = #{λ ⊆ k × m : |λ| = j}`,

and `coeff_gaussianBinomial_X_eq_boxCoeff` identifies `c_j` with the image of that natural number
in **any** semiring.  Two parameters, not `n` and `k`: the box form is symmetric under `k ↔ m`
(conjugation of partitions, `boxCoeff_transpose`), a symmetry that truncated subtraction destroys
in the `[n,k]` form.

## What is covered

* `coeff_gaussianBinomial_X_eq_boxCoeff`: `c_j = boxCoeff k m j` in every **semiring** — no
  commutativity, no ring, no characteristic and no order hypothesis.  (The corresponding
  stabilisation lemma `coeff_gaussianBinomial_X_eq_partitionCount` in `PartitionStabilization` is
  stated over a `CommRing`; only `Semiring` is ever used in its proof, and that is recorded here.)
* `boxCoeff_symm` and, in polynomial form, `coeff_gaussianBinomial_reflect` (proved in
  `GaussianBinomialPalindromic`): the **complete** second assertion `c_j = c_{D-j}` of
  `thm:qbinom-unimodal`, for all `k ≤ n`.
* `boxCoeff_le_succ_of_lt` and `boxCoeff_le_succ_of_lt_max`: an unconditional monotonicity step
  `c_j ≤ c_{j+1}`, valid for every `j + 1 ≤ max k m`.  This is the one genuinely new argument in
  the file: a bare-hands injection that adds one box to the largest part,
  `λ ↦ (λ_0 + 1, λ_1, …)`, which lands in the box precisely because `λ_0 ≤ |λ| = j < m`.
  Nothing in it is representation theory.
* `boxCoeffUnimodal_of_min_le_two`: the monotonicity step reaches the middle exactly when
  `k*m/2 ≤ max k m`, i.e. (given `min k m ≤ max k m`) when `min k m ≤ 2`.  So
  `thm:qbinom-unimodal` is proved **completely, including the unimodality half**, for every
  Gaussian coefficient `[n,k]_q` with `min(k, n-k) ≤ 2`: the columns `k = 0, 1, 2` and
  `k = n-2, n-1, n` of every Pascal row.  `coeff_gaussianBinomial_symm_unimodal_of_min_le_two`
  is the printed statement itself under that restriction, both halves together.
* `boxCoeffUnimodal_of_blockDecomposition`: the abstract shape of the printed `sl₂` argument.  If
  the coefficient sequence admits *any* decomposition into nonnegative multiples of the centred
  blocks `d ↦ [|2j - D| ≤ d]`, it is unimodal.  This is the last paragraph of the printed proof,
  isolated so that the single missing input is visible and nameable.

## What is NOT covered

* `lem:sl2-structure` (complete reducibility and the classification of the finite-dimensional
  complex `sl₂`-modules) is **not** formalised.  Mathlib has `Mathlib/Algebra/Lie/Sl2.lean`
  (`IsSl2Triple`, `HasPrimitiveVectorWith`, the `e`/`f` string relations), but no complete
  reducibility, no invariant Hermitian form, no integration to `SU(2)`, and no
  `IsSemisimpleModule` instance for Lie modules.  The printed proof is correct and standard; it
  states the Lie-algebra/Lie-group correspondence it uses in a single sentence, and it is that
  sentence that carries the formalisation cost.
* `prop:exterior-character` (`ch(⋀^k L_{n-1})(x) = x^{k(n-k)} [n,k]_{x^{-2}}`) is **not**
  formalised: it needs a weight-character ring `ℤ[x, x⁻¹]`, the `H`-action on an exterior power,
  and the weight decomposition of `exteriorPower`.  It is a module of its own and is useless
  without complete reducibility.
* Unimodality for `min(k, n-k) ≥ 3` is **not** proved and is not claimed anywhere below.  The
  first uncovered instance is `[6,3]_q = 1,1,2,3,3,3,3,2,1,1`, where the step `c_3 ≤ c_4` (namely
  `3 ≤ 3`) is true but unproved here: `min = 3`, `D/2 = 4`, and the injection reaches only
  `j + 1 ≤ max 3 3 = 3`.  The known routes are the `sl₂`/Proctor linear algebra or the
  O'Hara–Zeilberger injection.
* The inequalities are statements about natural numbers.  They transport to a general semiring
  only through the *values* `coeff_gaussianBinomial_X_eq_boxCoeff`, never as order statements: a
  semiring carries no order.

## Main declarations

* `boxCoeff`, `boxCoeff_eq_card`, `coeff_gaussianBinomial_X_eq_boxCoeff`,
  `coeff_gaussianBinomial_X_nat`.
* `boxCoeff_zero`, `boxCoeff_top`, `boxCoeff_symm`, `boxCoeff_transpose`,
  `boxCoeff_eq_partitionCount`.
* `boxCoeff_le_succ_of_lt`, `boxCoeff_le_succ_of_lt_max`,
  `coeff_gaussianBinomial_le_succ_of_lt_max`.
* `BoxCoeffUnimodal`, `boxCoeffUnimodal_def`, `boxCoeffUnimodal_of_min_le_two`,
  `boxCoeffUnimodal_one`, `boxCoeffUnimodal_two`,
  `coeff_gaussianBinomial_unimodal_of_min_le_two`,
  `coeff_gaussianBinomial_symm_unimodal_of_min_le_two`.
* `boxCoeffUnimodal_of_blockDecomposition`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### The coefficient dictionary -/

/-- `boxCoeff k m j` is the number of partitions of `j` fitting inside a `k × m` rectangle.
By `coeff_gaussianBinomial_X_eq_boxCoeff` this is the coefficient of `q^j` in `[m+k, k]_q`. -/
def boxCoeff (k m j : ℕ) : ℕ :=
  ((boxPartitions k m).filter fun l : Fin k → ℕ => ∑ i, l i = j).card

/-- Definitional unfolding of `boxCoeff`, so that no proof below has to rely on `simp` finding
the equation lemmas of a `def`. -/
theorem boxCoeff_eq_card (k m j : ℕ) :
    boxCoeff k m j = ((boxPartitions k m).filter fun l : Fin k → ℕ => ∑ i, l i = j).card :=
  rfl

/-- **The coefficient dictionary.**  Over *every* semiring the coefficient of `X^j` in the
universal Gaussian polynomial `[m+k, k]_X` is the number of partitions of `j` in a `k × m` box.
Only `Semiring R` is needed: no commutativity, no subtraction, no order. -/
theorem coeff_gaussianBinomial_X_eq_boxCoeff {R : Type*} [Semiring R] (k m j : ℕ) :
    (gaussianBinomial (X : R[X]) (m + k) k).coeff j = (boxCoeff k m j : R) := by
  rw [← sum_pow_boxSize_eq_gaussianBinomial, finsetSum_coeff]
  simp_rw [coeff_X_pow]
  rw [sum_boole, boxCoeff_eq_card]
  congr 2
  exact filter_congr fun l _ => eq_comm

/-- The dictionary at `R = ℕ`: the transfer bridge for every arithmetic statement below. -/
theorem coeff_gaussianBinomial_X_nat (k m j : ℕ) :
    (gaussianBinomial (X : ℕ[X]) (m + k) k).coeff j = boxCoeff k m j := by
  rw [coeff_gaussianBinomial_X_eq_boxCoeff, Nat.cast_id]

/-- The empty partition is the only one of size zero: `c_0 = 1`. -/
theorem boxCoeff_zero (k m : ℕ) : boxCoeff k m 0 = 1 := by
  rw [← coeff_gaussianBinomial_X_nat,
    coeff_gaussianBinomial_zero (R := ℕ) (Nat.le_add_left k m)]

/-! ### Symmetry: the second half of `thm:qbinom-unimodal`, in full -/

/-- **Symmetry** `c_j = c_{D-j}` with `D = k*m`, at the level of natural numbers.  Together with
`coeff_gaussianBinomial_reflect` this is the complete second assertion of `thm:qbinom-unimodal`
(complementation `λ ↦ (m - λ_{k-1}, …, m - λ_0)` inside the box, read off the palindromicity of
the Gaussian polynomial). -/
theorem boxCoeff_symm {k m j : ℕ} (hj : j ≤ k * m) :
    boxCoeff k m j = boxCoeff k m (k * m - j) := by
  have hk : k ≤ m + k := Nat.le_add_left k m
  have hmk : m + k - k = m := by omega
  have hj' : j ≤ k * (m + k - k) := by rw [hmk]; exact hj
  have h := coeff_gaussianBinomial_reflect (R := ℕ) hk hj'
  rw [hmk] at h
  simp only [coeff_gaussianBinomial_X_nat] at h
  exact h

/-- The full box is the only partition of size `k*m`: `c_D = 1`. -/
theorem boxCoeff_top (k m : ℕ) : boxCoeff k m (k * m) = 1 := by
  have h := boxCoeff_symm (k := k) (m := m) (j := 0) (Nat.zero_le _)
  rw [Nat.sub_zero, boxCoeff_zero] at h
  exact h.symm

/-- **Conjugation of partitions**: the box coefficients are symmetric in the two side lengths,
`#{λ ⊆ k × m : |λ| = j} = #{λ ⊆ m × k : |λ| = j}`.  This symmetry is invisible in the `[n,k]`
form, where the second side length is the truncated difference `n - k`. -/
theorem boxCoeff_transpose (k m j : ℕ) : boxCoeff k m j = boxCoeff m k j := by
  have hk : k ≤ m + k := Nat.le_add_left k m
  have hmk : m + k - k = m := by omega
  have hsymm : gaussianBinomial (X : ℕ[X]) (m + k) m = gaussianBinomial (X : ℕ[X]) (m + k) k := by
    have h := gaussianBinomial_symm (X : ℕ[X]) hk
    rw [hmk] at h
    exact h
  calc boxCoeff k m j
      = (gaussianBinomial (X : ℕ[X]) (m + k) k).coeff j :=
        (coeff_gaussianBinomial_X_nat k m j).symm
    _ = (gaussianBinomial (X : ℕ[X]) (m + k) m).coeff j := by rw [hsymm]
    _ = (gaussianBinomial (X : ℕ[X]) (k + m) m).coeff j := by rw [Nat.add_comm m k]
    _ = boxCoeff m k j := coeff_gaussianBinomial_X_nat m k j

/-- Stabilisation, in the box notation: for `N ≤ k` and `N ≤ m` the box coefficient of `N` is the
unrestricted partition count `p(N)`.  (This is `card_boxPartitions_filter_sum` renamed.) -/
theorem boxCoeff_eq_partitionCount {N k m : ℕ} (hk : N ≤ k) (hm : N ≤ m) :
    boxCoeff k m N = partitionCount N := by
  rw [boxCoeff_eq_card]
  exact card_boxPartitions_filter_sum hk hm

/-! ### The monotonicity step: adding one box to the largest part -/

/-- **The monotonicity step**, unconditional and elementary.  For a box of height `k+1` and
width `m`, and for every size `j < m`,

`#{λ ⊆ (k+1) × m : |λ| = j} ≤ #{λ ⊆ (k+1) × m : |λ| = j+1}`.

The injection adds one box to the largest part, `λ ↦ (λ_0 + 1, λ_1, …, λ_k)`.  It lands in the
box because `λ_0 ≤ |λ| = j < m`, it stays antitone because only the largest part grows, and it is
injective because the operation is invertible on the first coordinate.  The shape `k + 1` (rather
than a general height) is genuinely needed: a box of height `0` has
`boxCoeff 0 m 0 = 1 > 0 = boxCoeff 0 m 1`. -/
theorem boxCoeff_le_succ_of_lt {k m j : ℕ} (hj : j < m) :
    boxCoeff (k + 1) m j ≤ boxCoeff (k + 1) m (j + 1) := by
  simp only [boxCoeff_eq_card]
  have key : ∀ l ∈ (boxPartitions (k + 1) m).filter (fun l : Fin (k + 1) → ℕ => ∑ i, l i = j),
      (Fin.cons (l 0 + 1) (fun i : Fin k => l i.succ) : Fin (k + 1) → ℕ) ∈
        (boxPartitions (k + 1) m).filter (fun l : Fin (k + 1) → ℕ => ∑ i, l i = j + 1) := by
    intro l hl
    rw [Finset.mem_filter, mem_boxPartitions] at hl
    obtain ⟨⟨hle, hanti⟩, hsum⟩ := hl
    have h0 : l 0 ≤ ∑ i, l i :=
      Finset.single_le_sum (f := l) (fun i _ => Nat.zero_le _) (Finset.mem_univ 0)
    have hsl : ∑ i, l i = l 0 + ∑ i : Fin k, l i.succ := Fin.sum_univ_succ l
    rw [Finset.mem_filter, mem_boxPartitions]
    refine ⟨⟨fun i => ?_, fun a b hab => ?_⟩, ?_⟩
    · induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          omega
      | succ i =>
          simp only [Fin.cons_succ]
          exact hle i.succ
    · induction a using Fin.cases with
      | zero =>
          induction b using Fin.cases with
          | zero => exact le_rfl
          | succ b =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              have hb := hanti 0 b.succ (Fin.zero_le _)
              omega
      | succ a =>
          induction b using Fin.cases with
          | zero => exact absurd hab (by simp)
          | succ b =>
              simp only [Fin.cons_succ]
              exact hanti a.succ b.succ hab
    · show ∑ t, (Fin.cons (l 0 + 1) (fun i : Fin k => l i.succ) : Fin (k + 1) → ℕ) t = j + 1
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
  refine Finset.card_le_card_of_injOn
    (fun l : Fin (k + 1) → ℕ =>
      (Fin.cons (l 0 + 1) (fun i : Fin k => l i.succ) : Fin (k + 1) → ℕ)) ?_ ?_
  · intro l hl
    exact Finset.mem_coe.mpr (key l (Finset.mem_coe.mp hl))
  · intro l _ l' _ h
    funext i
    induction i using Fin.cases with
    | zero =>
        have h0 := congrFun h 0
        simp only [Fin.cons_zero] at h0
        omega
    | succ i =>
        have hs := congrFun h i.succ
        simp only [Fin.cons_succ] at hs
        exact hs

/-- **The monotonicity step in both orientations.**  For a nondegenerate box, `c_j ≤ c_{j+1}`
holds for every `j + 1 ≤ max k m`: apply `boxCoeff_le_succ_of_lt` to whichever side is the larger,
using `boxCoeff_transpose` to exchange the two.  Both positivity hypotheses are necessary: for
`k = 0` and `m ≥ 1` one has `j + 1 = 1 ≤ max 0 m` but `boxCoeff 0 m 0 = 1 > 0 = boxCoeff 0 m 1`. -/
theorem boxCoeff_le_succ_of_lt_max {k m j : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hj : j + 1 ≤ max k m) : boxCoeff k m j ≤ boxCoeff k m (j + 1) := by
  rcases le_total k m with hkm | hkm
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hjm : j < m := by omega
    exact boxCoeff_le_succ_of_lt hjm
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hjk : j < k := by omega
    rw [boxCoeff_transpose k (m' + 1) j, boxCoeff_transpose k (m' + 1) (j + 1)]
    exact boxCoeff_le_succ_of_lt hjk

/-- The monotonicity step for the Gaussian polynomial itself: for `0 < k < n`,
`c_j ≤ c_{j+1}` whenever `j + 1 ≤ max k (n-k)`. -/
theorem coeff_gaussianBinomial_le_succ_of_lt_max {n k j : ℕ} (hk : 0 < k) (hkn : k < n)
    (hj : j + 1 ≤ max k (n - k)) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff j ≤
      (gaussianBinomial (X : ℕ[X]) n k).coeff (j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have hm : 0 < m := by omega
  have hmk : m + k - k = m := by omega
  rw [hmk] at hj
  simp only [coeff_gaussianBinomial_X_nat]
  exact boxCoeff_le_succ_of_lt_max hk hm hj

/-! ### Unimodality -/

/-- The unimodality conclusion `c_0 ≤ c_1 ≤ ⋯ ≤ c_{⌊D/2⌋}` of `thm:qbinom-unimodal`, in
difference form, for the box of shape `k × m` (so `D = k*m`).  Naming it makes visible exactly
what is open: this predicate is *not* proved in general below. -/
def BoxCoeffUnimodal (k m : ℕ) : Prop :=
  ∀ j, j + 1 ≤ k * m / 2 → boxCoeff k m j ≤ boxCoeff k m (j + 1)

/-- Unfolding of `BoxCoeffUnimodal`. -/
theorem boxCoeffUnimodal_def (k m : ℕ) :
    BoxCoeffUnimodal k m ↔ ∀ j, j + 1 ≤ k * m / 2 → boxCoeff k m j ≤ boxCoeff k m (j + 1) :=
  Iff.rfl

/-- **Unimodality for thin boxes.**  If `min k m ≤ 2` then the box coefficients increase all the
way to the middle.  The reason the bound `min k m ≤ 2` is exactly right: writing `c = min k m`
and `M = max k m`, the elementary step `boxCoeff_le_succ_of_lt_max` covers `j + 1 ≤ M`, the middle
sits at `k*m/2 = c*M/2`, and — because `c ≤ M` always — `c*M/2 ≤ M` holds precisely when
`c ≤ 2`. -/
theorem boxCoeffUnimodal_of_min_le_two {k m : ℕ} (h : min k m ≤ 2) : BoxCoeffUnimodal k m := by
  refine (boxCoeffUnimodal_def k m).mpr fun j hj => ?_
  have hkm2 : 2 ≤ k * m := by omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  refine boxCoeff_le_succ_of_lt_max hkpos hmpos ?_
  rcases le_total k m with hkm | hkm
  · have hk2 : k ≤ 2 := by omega
    have hA : k * m ≤ 2 * m := Nat.mul_le_mul hk2 le_rfl
    omega
  · have hm2 : m ≤ 2 := by omega
    have hA : k * m ≤ k * 2 := Nat.mul_le_mul le_rfl hm2
    omega

/-- Unimodality for a box of height one (the coefficients are all `1`). -/
theorem boxCoeffUnimodal_one (m : ℕ) : BoxCoeffUnimodal 1 m :=
  boxCoeffUnimodal_of_min_le_two ((min_le_left 1 m).trans (by omega))

/-- Unimodality for a box of height two. -/
theorem boxCoeffUnimodal_two (m : ℕ) : BoxCoeffUnimodal 2 m :=
  boxCoeffUnimodal_of_min_le_two (min_le_left 2 m)

/-- **`thm:qbinom-unimodal`, unimodality half, for `min(k, n-k) ≤ 2`.**  For `k ≤ n` with
`min(k, n-k) ≤ 2`, the coefficient sequence of `[n,k]_X` increases up to the middle:
`c_j ≤ c_{j+1}` for every `j + 1 ≤ k(n-k)/2`.  Nothing is claimed for `min(k, n-k) ≥ 3`. -/
theorem coeff_gaussianBinomial_unimodal_of_min_le_two {n k : ℕ} (hk : k ≤ n)
    (h : min k (n - k) ≤ 2) {j : ℕ} (hj : j + 1 ≤ k * (n - k) / 2) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff j ≤
      (gaussianBinomial (X : ℕ[X]) n k).coeff (j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have hmk : m + k - k = m := by omega
  rw [hmk] at h hj
  simp only [coeff_gaussianBinomial_X_nat]
  exact (boxCoeffUnimodal_def k m).mp (boxCoeffUnimodal_of_min_le_two h) j hj

/-- **`thm:qbinom-unimodal` for `min(k, n-k) ≤ 2`, both halves at once.**  Symmetry
`c_j = c_{D-j}` (valid for all `k ≤ n`) together with unimodality `c_0 ≤ ⋯ ≤ c_{⌊D/2⌋}`.  This is
the printed statement restricted to the columns `k ≤ 2` and `k ≥ n-2` of every Pascal row; the
restriction is on the second conjunct only. -/
theorem coeff_gaussianBinomial_symm_unimodal_of_min_le_two {n k : ℕ} (hk : k ≤ n)
    (h : min k (n - k) ≤ 2) :
    (∀ j ≤ k * (n - k),
        (gaussianBinomial (X : ℕ[X]) n k).coeff j =
          (gaussianBinomial (X : ℕ[X]) n k).coeff (k * (n - k) - j)) ∧
      ∀ j, j + 1 ≤ k * (n - k) / 2 →
        (gaussianBinomial (X : ℕ[X]) n k).coeff j ≤
          (gaussianBinomial (X : ℕ[X]) n k).coeff (j + 1) :=
  ⟨fun _ hj => coeff_gaussianBinomial_reflect hk hj,
    fun _ hj => coeff_gaussianBinomial_unimodal_of_min_le_two hk h hj⟩

/-! ### The `sl₂` skeleton as an abstract reduction -/

/-- **The centred-block criterion**: the combinatorial content of the printed `sl₂` proof,
isolated from the representation theory.

Suppose the coefficient sequence of a `k × m` box admits *any* decomposition

`c_i = ∑_{d ≤ D} mult d · [ 2i ≤ D + d and D ≤ 2i + d ]`,  `D = k*m`,

with nonnegative multiplicities `mult d`.  The bracket is the indicator of `|2i - D| ≤ d`, i.e.
of the centred block of weights `d, d-2, …, -d` sitting inside the ambient weight string
`D, D-2, …, -D`.  Moving from `i` to `i+1` while `2(i+1) ≤ D` can only switch a block on, never
off; hence unimodality.

In the printed proof the decomposition is supplied by `lem:sl2-structure` and
`prop:exterior-character`: `mult d` is the multiplicity of the irreducible `L_d` in
`⋀^k L_{n-1}`.  **Neither of those is formalised here**, and no instance of this hypothesis is
constructed in this file; the lemma exists to name the exact missing input.  The hypothesis is
satisfiable — for `k = m = 1` take `mult = fun d => if d = 1 then 1 else 0` — so the statement is
not vacuous. -/
theorem boxCoeffUnimodal_of_blockDecomposition {k m : ℕ} (mult : ℕ → ℕ)
    (hdec : ∀ i ≤ k * m, boxCoeff k m i =
      ∑ d ∈ range (k * m + 1),
        mult d * (if 2 * i ≤ k * m + d ∧ k * m ≤ 2 * i + d then 1 else 0)) :
    BoxCoeffUnimodal k m := by
  refine (boxCoeffUnimodal_def k m).mpr fun j hj => ?_
  have hj2 : 2 * (j + 1) ≤ k * m := by omega
  rw [hdec j (by omega), hdec (j + 1) (by omega)]
  refine Finset.sum_le_sum fun d _ => Nat.mul_le_mul le_rfl ?_
  split_ifs <;> omega

end Fabius
