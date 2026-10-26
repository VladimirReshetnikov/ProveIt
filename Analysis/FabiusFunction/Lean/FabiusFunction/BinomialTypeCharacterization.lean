import FabiusFunction.BinomialType
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots

/-!
# The generating-function characterization of binomial type

Let `K` be a characteristic-zero domain that is a `ℚ`-algebra (a field of
characteristic zero, say) and `(p_n)` polynomials in `K[x]` with `p_0 = 1`.
This module proves the equivalence

  `p_n(x + y) = ∑_k C(n,k) p_k(x) p_{n-k}(y)` for all `x, y ∈ K`, `n`
  ⟺ `∑_n p_n(x) t^n/n! = exp(x B(t))` for all `x`, for some `B ∈ t K[[t]]`,

together with the uniqueness of `B` — it is `B(t) = ∑_n p_n'(0) t^n/n!`, the
exponential generating function of the *linear coefficients* of the `p_n` —
and the degree clause: `deg p_n ≤ n` always, and `deg p_n = n` for every `n`
if and only if `B'(0) ≠ 0` (the linear coefficient of `p_1`).  This is
`thm:merged-binomial-type-characterization` of the combinatorial-coefficient
calculus manuscript.  Module `BinomialType` proves the forward direction for
the Bell-derived sequences `p_n(x) = B_n(a_1 x, a_2 x, …)`; the content here
is the converse: the binomial identity alone forces the exponential shape.

## The route: columns, not logarithms

The manuscript takes the logarithm of `P(x,t) = ∑ p_n(x) t^n/n!` in `K[x][[t]]`
and shows the log is linear in `x`.  We avoid `exp`/`log` over `K[x]` and
instead read the binomial identity off the *columns* of the coefficient
matrix `c_{n,j} = [x^j] p_n(x)`.  Writing `C_j(t) = ∑_n c_{n,j} t^n/n!`
(`columnSeries`), the binomial identity is equivalent to the
coefficient-of-`x^i y^j` identity

  `C(i+j, j) · C_{i+j}(t) = C_i(t) · C_j(t)`

(`choose_smul_columnSeries_add`), extracted through two polynomial
evaluations at infinitely many points (`Polynomial.funext`), the Taylor
shift `p_n(x + Y) = ∑_j (D^{(j)} p_n)(x) Y^j` and the Hasse-derivative
coefficient formula.  With `(i,j) = (0,0)` and `p_0 = 1` this gives `C_0 = 1`
(a unit idempotent); with `i = 1` it gives `(j+1) C_{j+1} = C_1 C_j`, so
`j! C_j = C_1^j`.  Since `C_1(t) = ∑_{n ≥ 1} c_{n,1} t^n/n!` is the Bell weight
series of the linear coefficients `a_n = c_{n,1}`, the partial Bell column
theorem `bellWeightSeries_pow` identifies `c_{n,j} = B_{n,j}(a)`, hence
`p_n(x) = B_n(a_1 x, a_2 x, …)` and the forward module supplies the EGF.  The
exponential shape is thus a *consequence of the column recursion*, and the
proof works verbatim over any domain that is a `ℚ`-algebra.

## Main results

* `IsBinomialType`: the binomial identity, over any commutative semiring.
* `linearCoeff`: the weights `a_n = [x] p_n`; `columnSeries`: the column EGFs.
* `choose_mul_coeff_eq_sum_of_isBinomialType`: the coefficient form of the
  binomial identity, `C(i+j,j) c_{n,i+j} = ∑_k C(n,k) c_{k,i} c_{n-k,j}`.
* `choose_smul_columnSeries_add`, `columnSeries_zero_eq_one`,
  `factorial_smul_columnSeries`: the column recursion and `j! C_j = C_1^j`.
* `coeff_eq_partialBell_of_isBinomialType`: `[x^k] p_n = B_{n,k}(a)`.
* `eval_eq_binomialTypePoly_of_isBinomialType`: `p_n = B_n(a_1 x, a_2 x, …)`.
* `egfA_eval_eq_exp_subst_of_isBinomialType`: the EGF `exp(x B(t))` with
  `B = egfA (linearCoeff p)`.
* `isBinomialType_of_egfA_eq`: the converse direction (2) ⟹ (1), over any
  commutative `ℚ`-algebra.
* `eq_egfA_linearCoeff_of_egfA_eq`: uniqueness of `B`.
* `isBinomialType_iff_exists_egfA_eq`, `isBinomialType_iff_existsUnique_egfA_eq`:
  the theorem.
* `natDegree_le_of_isBinomialType`, `natDegree_eq_iff_of_isBinomialType`,
  `natDegree_eq_iff_coeff_one_ne_zero_of_egfA_eq`: the degree clause.
* Helpers: `egfA_injective`, `bellWeightSeries_factorial_mul_coeff`
  (`B = ∑ b_n t^n/n!` with `b_n = n! [t^n] B`), `partialBell_add_one_one`.

## Not covered

* `prop:merged-abel` (Abel polynomials `x(x - na)^{n-1}` are of binomial type)
  needs Lagrange–Bürmann or Abel's binomial identity and is not proved here.
* The manuscript's logarithmic proof (`L(x,t) = log P(x,t)` is linear in `x`)
  is replaced by the column argument above; no formal `log` over `K[x]` is used.
-/

set_option autoImplicit false

open Finset PowerSeries
open scoped Polynomial

namespace Fabius

/-! ### The binomial identity and the linear coefficients -/

section Defs

variable {R : Type*} [CommSemiring R]

/-- A polynomial sequence `p` is **of binomial type** when
`p_n(x + y) = ∑_{k ≤ n} C(n,k) p_k(x) p_{n-k}(y)` for all `x, y ∈ R` and all `n`.
(The normalization `p_0 = 1` is a separate hypothesis in the results below.) -/
def IsBinomialType (p : ℕ → R[X]) : Prop :=
  ∀ (x y : R) (n : ℕ), (p n).eval (x + y) =
    ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * ((p k).eval x * (p (n - k)).eval y)

/-- The **linear coefficients** `a_n = [x] p_n(x) = p_n'(0)` of a polynomial sequence:
the weights of its Bell representation. -/
def linearCoeff (p : ℕ → R[X]) (n : ℕ) : R := (p n).coeff 1

/-- `a_0 = 0` when `p_0 = 1`. -/
theorem linearCoeff_zero {p : ℕ → R[X]} (hp0 : p 0 = 1) : linearCoeff p 0 = 0 := by
  simp [linearCoeff, hp0, Polynomial.coeff_one]

/-- `B_{n+1,1}(x) = x_{n+1}`: a single block carries the whole set. -/
theorem partialBell_add_one_one (x : ℕ → R) (n : ℕ) : partialBell x (n + 1) 1 = x (n + 1) := by
  rw [partialBell_succ_succ, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
    rw [hm, partialBell_succ_zero, mul_zero, mul_zero]

end Defs

/-! ### Column series and generating-function helpers -/

section Columns

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The **`j`-th column series** `C_j(t) = ∑_n ([x^j] p_n) t^n/n!` of a polynomial
sequence: the exponential generating function of the `j`-th coefficient column. -/
noncomputable def columnSeries (p : ℕ → K[X]) (j : ℕ) : K⟦X⟧ :=
  egfA K fun n => (p n).coeff j

/-- The exponential generating series determines the sequence. -/
theorem egfA_injective : Function.Injective (egfA K) := by
  intro a b h
  funext n
  have hc := congrArg (coeff n) h
  rw [coeff_egfA, coeff_egfA] at hc
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hinv : algebraMap ℚ K n.factorial * algebraMap ℚ K (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel hn, map_one]
  calc a n = (algebraMap ℚ K n.factorial * algebraMap ℚ K (1 / n.factorial)) * a n := by
        rw [hinv, one_mul]
    _ = algebraMap ℚ K n.factorial * (algebraMap ℚ K (1 / n.factorial) * a n) := by ring
    _ = algebraMap ℚ K n.factorial * (algebraMap ℚ K (1 / n.factorial) * b n) := by rw [hc]
    _ = b n := by rw [← mul_assoc, hinv, one_mul]

/-- A series without constant term is the Bell weight series of the weights
`b_n = n! · [t^n] B`. -/
theorem bellWeightSeries_factorial_mul_coeff {B : K⟦X⟧} (hB : constantCoeff B = 0) :
    bellWeightSeries K (fun n => (n.factorial : K) * coeff n B) = B := by
  ext n
  rw [bellWeightSeries, coeff_egfA]
  cases n with
  | zero => rw [if_pos rfl, mul_zero, coeff_zero_eq_constantCoeff_apply, hB]
  | succ n =>
    have hne : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    rw [if_neg (by omega : n + 1 ≠ 0), ← mul_assoc,
      ← map_natCast (algebraMap ℚ K) (n + 1).factorial, ← map_mul, one_div_mul_cancel hne,
      map_one, one_mul]

/-- When `p_0 = 1` the Bell weight series of the linear coefficients is simply
their exponential generating series (the `j = 0` term vanishes anyway). -/
theorem bellWeightSeries_linearCoeff {p : ℕ → K[X]} (hp0 : p 0 = 1) :
    bellWeightSeries K (linearCoeff p) = egfA K (linearCoeff p) := by
  rw [bellWeightSeries]
  congr 1
  funext n
  cases n with
  | zero => simp [linearCoeff, hp0, Polynomial.coeff_one]
  | succ n => simp

/-- The first column series is the Bell weight series of the linear coefficients. -/
theorem columnSeries_one {p : ℕ → K[X]} (hp0 : p 0 = 1) :
    columnSeries p 1 = bellWeightSeries K (linearCoeff p) := by
  rw [bellWeightSeries_linearCoeff hp0]
  rfl

/-- **(2) ⟹ Bell form.** If `∑_n p_n(x) t^n/n! = exp(x B(t))` for every `x`, with
`B(0) = 0`, then `p_n(x) = B_n(b_1 x, b_2 x, …)` with `b_n = n! [t^n] B`. -/
theorem eval_eq_binomialTypePoly_of_egfA_eq {p : ℕ → K[X]} {B : K⟦X⟧}
    (hB : constantCoeff B = 0)
    (h : ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B)) (x : K) (n : ℕ) :
    (p n).eval x = binomialTypePoly (fun m => (m.factorial : K) * coeff m B) x n := by
  have h' := h x
  rw [← bellWeightSeries_factorial_mul_coeff hB,
    exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly] at h'
  exact congrFun (egfA_injective h') n

/-- **(2) ⟹ (1), over any commutative `ℚ`-algebra:** a polynomial sequence whose
exponential generating function is `exp(x B(t))` for every `x`, with `B(0) = 0`,
satisfies the binomial identity. -/
theorem isBinomialType_of_egfA_eq {p : ℕ → K[X]} {B : K⟦X⟧} (hB : constantCoeff B = 0)
    (h : ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B)) :
    IsBinomialType p := by
  intro x y n
  rw [eval_eq_binomialTypePoly_of_egfA_eq hB h, binomialTypePoly_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_eq_binomialTypePoly_of_egfA_eq hB h, eval_eq_binomialTypePoly_of_egfA_eq hB h]

end Columns

/-! ### The converse: the binomial identity forces the exponential shape -/

section Converse

variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K] [Algebra ℚ K]
variable {p : ℕ → K[X]}

/-- The binomial identity as a Taylor expansion in the second variable:
`p_n(x + Y) = ∑_k C(n,k) p_k(x) p_{n-k}(Y)` in `K[Y]`, for every `x ∈ K`. -/
theorem taylor_eq_of_isBinomialType (hp : IsBinomialType p) (x : K) (n : ℕ) :
    Polynomial.taylor x (p n) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((n.choose k : K) * (p k).eval x) * p (n - k) := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro y
  rw [Polynomial.taylor_eval, add_comm y x, hp x y n, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- Reading the coefficient of `Y^j` in the Taylor form: the `j`-th Hasse derivative
of `p_n` is `∑_k C(n,k) ([x^j] p_{n-k}) p_k`, an identity in `K[x]`. -/
theorem hasseDeriv_eq_of_isBinomialType (hp : IsBinomialType p) (j n : ℕ) :
    Polynomial.hasseDeriv j (p n) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((n.choose k : K) * (p (n - k)).coeff j) * p k := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  have h := congrArg (fun q : K[X] => q.coeff j) (taylor_eq_of_isBinomialType hp x n)
  simp only [Polynomial.taylor_coeff, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h
  rw [h, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- **The coefficient form of the binomial identity:** with `c_{n,j} = [x^j] p_n`,
`C(i+j, j) · c_{n,i+j} = ∑_k C(n,k) c_{k,i} c_{n-k,j}` (the coefficient of `x^i y^j`). -/
theorem choose_mul_coeff_eq_sum_of_isBinomialType (hp : IsBinomialType p) (i j n : ℕ) :
    ((i + j).choose j : K) * (p n).coeff (i + j) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * ((p k).coeff i * (p (n - k)).coeff j) := by
  have h := congrArg (fun q : K[X] => q.coeff i) (hasseDeriv_eq_of_isBinomialType hp j n)
  simp only [Polynomial.hasseDeriv_coeff, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The column recursion:** `C(i+j, j) · C_{i+j}(t) = C_i(t) · C_j(t)`, the
binomial identity read on the column generating functions. -/
theorem choose_smul_columnSeries_add (hp : IsBinomialType p) (i j : ℕ) :
    ((i + j).choose j : K) • columnSeries p (i + j) = columnSeries p i * columnSeries p j := by
  unfold columnSeries
  rw [egfA_mul]
  ext n
  rw [coeff_smul, coeff_egfA, coeff_egfA, smul_eq_mul]
  have hb : Bell.binomialConv (fun m => (p m).coeff i) (fun m => (p m).coeff j) n
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * ((p k).coeff i * (p (n - k)).coeff j) :=
    rfl
  rw [hb, ← choose_mul_coeff_eq_sum_of_isBinomialType hp i j n]
  ring

/-- `C_0 = 1`: the constant-term column is an idempotent unit, hence `1`.
Equivalently `p_n(0) = 0` for `n ≥ 1`. -/
theorem columnSeries_zero_eq_one (hp : IsBinomialType p) (hp0 : p 0 = 1) :
    columnSeries p 0 = 1 := by
  have h := choose_smul_columnSeries_add hp 0 0
  rw [add_zero, Nat.choose_zero_right, Nat.cast_one, one_smul] at h
  have hu : IsUnit (columnSeries p 0) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [columnSeries, hp0]
  have h2 : columnSeries p 0 * 1 = columnSeries p 0 * columnSeries p 0 := by
    rw [mul_one]
    exact h
  exact (hu.mul_left_cancel h2).symm

/-- **`j! · C_j = C_1^j`:** the columns are the powers of the first column. -/
theorem factorial_smul_columnSeries (hp : IsBinomialType p) (hp0 : p 0 = 1) (j : ℕ) :
    (j.factorial : K) • columnSeries p j = columnSeries p 1 ^ j := by
  induction j with
  | zero =>
    rw [Nat.factorial_zero, Nat.cast_one, one_smul, pow_zero, columnSeries_zero_eq_one hp hp0]
  | succ j ih =>
    have h := choose_smul_columnSeries_add hp 1 j
    rw [add_comm 1 j, Nat.choose_succ_self_right] at h
    calc ((j + 1).factorial : K) • columnSeries p (j + 1)
        = (j.factorial : K) • (((j + 1 : ℕ) : K) • columnSeries p (j + 1)) := by
          rw [smul_smul, ← Nat.cast_mul, Nat.factorial_succ, mul_comm]
      _ = (j.factorial : K) • (columnSeries p 1 * columnSeries p j) := by rw [h]
      _ = columnSeries p 1 * ((j.factorial : K) • columnSeries p j) := by rw [mul_smul_comm]
      _ = columnSeries p 1 ^ (j + 1) := by rw [ih, pow_succ']

/-- **The coefficients are partial Bell polynomials:** `[x^k] p_n = B_{n,k}(a)` with
`a = linearCoeff p`.  From `k! C_k = C_1^k` and the partial Bell column theorem. -/
theorem coeff_eq_partialBell_of_isBinomialType (hp : IsBinomialType p) (hp0 : p 0 = 1)
    (n k : ℕ) : (p n).coeff k = partialBell (linearCoeff p) n k := by
  have h := factorial_smul_columnSeries hp hp0 k
  rw [columnSeries_one hp0, bellWeightSeries_pow] at h
  have hc := congrArg (coeff n) h
  simp only [columnSeries, coeff_smul, coeff_egfA, smul_eq_mul] at hc
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hinv : algebraMap ℚ K (n.factorial / k.factorial) *
      ((k.factorial : K) * algebraMap ℚ K (1 / n.factorial)) = 1 := by
    rw [← map_natCast (algebraMap ℚ K) k.factorial, ← map_mul, ← map_mul,
      ← map_one (algebraMap ℚ K)]
    congr 1
    field_simp
  calc (p n).coeff k
      = (algebraMap ℚ K (n.factorial / k.factorial) *
          ((k.factorial : K) * algebraMap ℚ K (1 / n.factorial))) * (p n).coeff k := by
        rw [hinv, one_mul]
    _ = algebraMap ℚ K (n.factorial / k.factorial) *
          ((k.factorial : K) * (algebraMap ℚ K (1 / n.factorial) * (p n).coeff k)) := by
        ring
    _ = algebraMap ℚ K (n.factorial / k.factorial) *
          ((k.factorial : K) *
            (algebraMap ℚ K (1 / n.factorial) * partialBell (linearCoeff p) n k)) := by
        rw [hc]
    _ = (algebraMap ℚ K (n.factorial / k.factorial) *
          ((k.factorial : K) * algebraMap ℚ K (1 / n.factorial))) *
            partialBell (linearCoeff p) n k := by
        ring
    _ = partialBell (linearCoeff p) n k := by rw [hinv, one_mul]

/-- **`deg p_n ≤ n`** for a sequence of binomial type. -/
theorem natDegree_le_of_isBinomialType (hp : IsBinomialType p) (hp0 : p 0 = 1) (n : ℕ) :
    (p n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_eq_partialBell_of_isBinomialType hp hp0, partialBell_eq_zero_of_lt _ hN]

/-- **Every sequence of binomial type is Bell-derived:**
`p_n(x) = B_n(a_1 x, a_2 x, …)` with `a = linearCoeff p`. -/
theorem eval_eq_binomialTypePoly_of_isBinomialType (hp : IsBinomialType p) (hp0 : p 0 = 1)
    (x : K) (n : ℕ) : (p n).eval x = binomialTypePoly (linearCoeff p) x n := by
  rw [binomialTypePoly_eq_sum,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_le_of_isBinomialType hp hp0 n))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_eq_partialBell_of_isBinomialType hp hp0]

/-- **(1) ⟹ (2):** a sequence of binomial type has exponential generating function
`exp(x B(t))` with `B(t) = ∑_{n ≥ 1} p_n'(0) t^n/n!`, the EGF of the linear coefficients. -/
theorem egfA_eval_eq_exp_subst_of_isBinomialType (hp : IsBinomialType p) (hp0 : p 0 = 1)
    (x : K) : egfA K (fun n => (p n).eval x) = (exp K).subst (x • egfA K (linearCoeff p)) := by
  rw [← bellWeightSeries_linearCoeff hp0, exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly]
  congr 1
  funext n
  exact eval_eq_binomialTypePoly_of_isBinomialType hp hp0 x n

/-- **Uniqueness of `B`:** any `B ∈ t K[[t]]` with `∑_n p_n(x) t^n/n! = exp(x B(t))` for
all `x` is the EGF of the linear coefficients, `B(t) = ∑_n p_n'(0) t^n/n!`. -/
theorem eq_egfA_linearCoeff_of_egfA_eq (hp0 : p 0 = 1) {B : K⟦X⟧} (hB : constantCoeff B = 0)
    (h : ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B)) :
    B = egfA K (linearCoeff p) := by
  have hpoly : ∀ n, p n = ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (partialBell (fun m => (m.factorial : K) * coeff m B) n k) *
        Polynomial.X ^ k := by
    intro n
    haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    apply Polynomial.funext
    intro x
    rw [eval_eq_binomialTypePoly_of_egfA_eq hB h x n, binomialTypePoly_eq_sum,
      Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hfun : (fun m => (m.factorial : K) * coeff m B) = linearCoeff p := by
    funext n
    cases n with
    | zero =>
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff_apply,
        hB, linearCoeff_zero hp0]
    | succ n =>
      rw [linearCoeff, hpoly (n + 1), Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
      rw [if_pos (by omega : 1 < n + 1 + 1), partialBell_add_one_one]
  rw [← bellWeightSeries_factorial_mul_coeff hB, hfun, bellWeightSeries_linearCoeff hp0]

/-- **Generating-function characterization of binomial type** (existence form):
for polynomials `p_n ∈ K[x]` with `p_0 = 1`, the binomial identity holds for all
`x, y` iff there is `B ∈ t K[[t]]` with `∑_n p_n(x) t^n/n! = exp(x B(t))` for all `x`. -/
theorem isBinomialType_iff_exists_egfA_eq (p : ℕ → K[X]) (hp0 : p 0 = 1) :
    IsBinomialType p ↔ ∃ B : K⟦X⟧, constantCoeff B = 0 ∧
      ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B) := by
  constructor
  · intro hp
    refine ⟨egfA K (linearCoeff p), ?_, egfA_eval_eq_exp_subst_of_isBinomialType hp hp0⟩
    rw [constantCoeff_egfA, linearCoeff_zero hp0]
  · rintro ⟨B, hB, h⟩
    exact isBinomialType_of_egfA_eq hB h

/-- **Generating-function characterization of binomial type** (uniqueness form):
the series `B` of `isBinomialType_iff_exists_egfA_eq` is unique. -/
theorem isBinomialType_iff_existsUnique_egfA_eq (p : ℕ → K[X]) (hp0 : p 0 = 1) :
    IsBinomialType p ↔ ∃! B : K⟦X⟧, constantCoeff B = 0 ∧
      ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B) := by
  rw [isBinomialType_iff_exists_egfA_eq p hp0]
  constructor
  · rintro ⟨B, hB, h⟩
    refine ⟨B, ⟨hB, h⟩, fun B' hB' => ?_⟩
    rw [eq_egfA_linearCoeff_of_egfA_eq hp0 hB'.1 hB'.2, eq_egfA_linearCoeff_of_egfA_eq hp0 hB h]
  · rintro ⟨B, ⟨hB, h⟩, -⟩
    exact ⟨B, hB, h⟩

/-- **The degree clause:** for a sequence of binomial type, `deg p_n = n` for every `n`
iff the linear coefficient `a_1 = p_1'(0)` is nonzero.  The leading coefficient of
`p_n` is `a_1^n`. -/
theorem natDegree_eq_iff_of_isBinomialType (hp : IsBinomialType p) (hp0 : p 0 = 1) :
    (∀ n, (p n).natDegree = n) ↔ linearCoeff p 1 ≠ 0 := by
  constructor
  · intro hdeg h1
    have hne : p 1 ≠ 0 := by
      intro h0
      have h := hdeg 1
      rw [h0, Polynomial.natDegree_zero] at h
      exact zero_ne_one h
    apply Polynomial.leadingCoeff_ne_zero.mpr hne
    rw [← Polynomial.coeff_natDegree, hdeg 1]
    exact h1
  · intro h1 n
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_of_isBinomialType hp hp0 n)
    rw [coeff_eq_partialBell_of_isBinomialType hp hp0, partialBell_self]
    exact pow_ne_zero n h1

/-- `B'(0) = [t] B` is the linear coefficient of `p_1`. -/
theorem coeff_one_eq_linearCoeff_of_egfA_eq (hp0 : p 0 = 1) {B : K⟦X⟧}
    (hB : constantCoeff B = 0)
    (h : ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B)) :
    coeff 1 B = linearCoeff p 1 := by
  rw [eq_egfA_linearCoeff_of_egfA_eq hp0 hB h, coeff_egfA]
  simp

/-- **The degree clause in terms of `B`:** `deg p_n = n` for every `n` iff `B'(0) ≠ 0`,
i.e. iff `B` is a delta series. -/
theorem natDegree_eq_iff_coeff_one_ne_zero_of_egfA_eq (hp0 : p 0 = 1) {B : K⟦X⟧}
    (hB : constantCoeff B = 0)
    (h : ∀ x : K, egfA K (fun n => (p n).eval x) = (exp K).subst (x • B)) :
    (∀ n, (p n).natDegree = n) ↔ coeff 1 B ≠ 0 := by
  rw [coeff_one_eq_linearCoeff_of_egfA_eq hp0 hB h]
  exact natDegree_eq_iff_of_isBinomialType (isBinomialType_of_egfA_eq hB h) hp0

end Converse

end Fabius
