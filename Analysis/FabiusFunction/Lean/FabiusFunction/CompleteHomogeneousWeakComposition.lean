import FabiusFunction.CompleteHomogeneous
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Complete homogeneous evaluations as sums over weak compositions

For a finite family `a : ι → R`, the degree-`n` complete homogeneous
evaluation is

`h_n(a) = ∑_{c : ι → ℕ, ∑ i, c i = n} ∏ i, a i ^ c i`.

The sum is the finite set `Finset.piAntidiag Finset.univ n` already provided
by Mathlib. For `ι = Fin k`, it is also Mathlib's
`Finset.Nat.antidiagonalTuple k n`, the finite set of all `k`-tuples of
nonnegative integers with sum `n`. Zero coordinates and empty families
are included; no positivity or nonzeroness assumption is made on the values.

The proof reindexes the multiset definition of `completeHomogeneousEval`
by the count of each variable. Mathlib's `Finset.map_sym_eq_piAntidiag`
provides this bijection, and `Finset.prod_multiset_map_count` groups repeated
factors into powers. Thus every weak composition occurs once, with no
multinomial coefficient.

This supplies the explicit weak-composition sum in
`eq:second-complete-symmetric` of the canonical
`Combinatorial_Coefficient_Calculus` monograph, after substituting
`a j = j + 1` and using the Stirling/complete-homogeneous bridge.

## Main results

* `completeHomogeneousEval_eq_sum_piAntidiag`: arbitrary finite index types.
* `completeHomogeneousEvalOn_eq_sum_piAntidiag`: a family indexed by a finset.
* `completeHomogeneousEval_fin_eq_sum_antidiagonalTuple`: explicit tuples.
* `completeHomogeneousEvalOn_range_eq_sum_antidiagonalTuple`: the range-indexed
  form used by Stirling columns.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- **Complete homogeneous evaluations are sums over weak compositions.**

`Finset.piAntidiag Finset.univ n` consists exactly of the functions
`c : ι → ℕ` satisfying `∑ i, c i = n`. Grouping the repeated factors of
each multiset gives its monomial `∏ i, a i ^ c i` once. The identity holds
over every commutative semiring, including all empty-family cases. -/
theorem completeHomogeneousEval_eq_sum_piAntidiag
    {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (n : ℕ) :
    completeHomogeneousEval a n =
      ∑ c ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        ∏ i, a i ^ c i := by
  classical
  rw [← Finset.map_sym_eq_piAntidiag (Finset.univ : Finset ι) n,
    Finset.sum_map, Finset.sym_univ]
  unfold completeHomogeneousEval
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero_of_not_mem hi, pow_zero]

/-- **Weak-composition formula for a family indexed by a finset.**

The exponent functions are defined on the subtype `s`; their coordinates
sum to `n`. Thus elements outside `s` introduce neither variables nor
additional exponent choices. The ambient index type need not be finite. -/
theorem completeHomogeneousEvalOn_eq_sum_piAntidiag
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (a : ι → R) (n : ℕ) :
    completeHomogeneousEvalOn s a n =
      ∑ c ∈ Finset.piAntidiag (Finset.univ : Finset s) n,
        ∏ i : s, a i ^ c i := by
  exact completeHomogeneousEval_eq_sum_piAntidiag (fun i : s => a i) n

/-- **Explicit tuple formula for complete homogeneous evaluations.**

`Finset.Nat.antidiagonalTuple k n` is exactly the finite set of functions
`c : Fin k → ℕ` with `∑ i, c i = n`, so this is the usual sum of the
monomials `a₁^c₁ ··· a_k^c_k` over all weak compositions of `n`. -/
theorem completeHomogeneousEval_fin_eq_sum_antidiagonalTuple
    {R : Type*} [CommSemiring R] {k : ℕ} (a : Fin k → R) (n : ℕ) :
    completeHomogeneousEval a n =
      ∑ c ∈ Finset.Nat.antidiagonalTuple k n, ∏ i, a i ^ c i := by
  rw [completeHomogeneousEval_eq_sum_piAntidiag,
    Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]

/-- **Range-indexed complete homogeneous evaluations as weak-composition sums.**

This is the form of the explicit sum in `eq:second-complete-symmetric`:
specializing `a j` to `j + 1` gives `∑ c, 1^c₁ ··· k^c_k`. -/
theorem completeHomogeneousEvalOn_range_eq_sum_antidiagonalTuple
    {R : Type*} [CommSemiring R] (a : ℕ → R) (k n : ℕ) :
    completeHomogeneousEvalOn (Finset.range k) a n =
      ∑ c ∈ Finset.Nat.antidiagonalTuple k n, ∏ i : Fin k, a i ^ c i := by
  rw [completeHomogeneousEvalOn_range,
    completeHomogeneousEval_fin_eq_sum_antidiagonalTuple]

end Fabius
