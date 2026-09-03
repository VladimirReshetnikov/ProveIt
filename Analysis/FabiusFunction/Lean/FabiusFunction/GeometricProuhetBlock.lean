import FabiusFunction.ThueMorseSparseProuhet

/-!
# The geometric-step Prouhet block

`ThueMorseSparseProuhet` proves Prouhet annihilation and the sharp moment for
an *arbitrary* family of step weights `w : ι → R` over an arbitrary commutative
ring, and the Thue--Morse layer instantiates it at the dyadic steps `w j = 2^j`.
This module records the instantiation at the **geometric** steps `w j = q^j`
for an arbitrary `q`, in which the nodes

`x + ∑_{j ∈ T} q^j`,  `T ⊆ {0, …, k-1}`,

are the base-`q` numbers with digits `0` and `1`, translated by `x`.  At `q = 2`
they are exactly `x + r` for `r < 2^k`, which is the dyadic block; at general
`q` they are its natural deformation.

The whole content beyond the engine is one exponent identity,

`∏_{j<k} q^j = q^{C(k,2)}`  (`prod_range_pow_eq_pow_choose_two`),

which is where the triangular power in the sharp moment comes from.  It also
explains, retroactively, the constant `4^{C(k,2)} = 2^{2C(k,2)}` in the dyadic
q-binomial--Thue--Morse formula of `FabiusQBinomialFormula`: the dyadic block's
sharp moment carries `2^{C(k,2)}`, and the formula's weight carries its square.

These statements discharge part of the formalization obligation recorded for
the general-nome value identity in the research-frontier volume: the inner
block of that conjectured identity is the geometric-step block at
`w j = q^{-j}`, which is this module at `q⁻¹`.  What remains open there is the
left-hand side -- a nome-general replacement for the base-two half-moment
recursion -- not the block.

## Main results

* `prod_range_pow_eq_pow_choose_two` — `∏_{j<k} a^j = a^{C(k,2)}` in any
  commutative monoid.
* `sum_powerset_geometric_eval_eq_zero_of_degree_lt` — Prouhet annihilation at
  geometric steps, for every polynomial of degree below `k`.
* `sum_powerset_geometric_pow_card` — the sharp moment
  `(-1)^k k! q^{C(k,2)}`, independent of the translation.
* `sum_powerset_geometric_eval_eq_coeff` — the unified coefficient extractor.
* `sum_powerset_two_geometric_pow_card` — the dyadic case `q = 2`, recovering
  the classical Prouhet constant `(-1)^k k! 2^{C(k,2)}`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The triangular power.**  In any commutative monoid,
`∏_{j<k} a^j = a^{C(k,2)}`, since `∑_{j<k} j = k(k-1)/2 = C(k,2)`.  The
natural-number division in Gauss' formula is exact because `k(k-1)` is
even. -/
theorem prod_range_pow_eq_pow_choose_two {M : Type*} [CommMonoid M]
    (a : M) (k : ℕ) :
    ∏ j ∈ Finset.range k, a ^ j = a ^ k.choose 2 := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, ← Nat.choose_two_right]

/-- **Prouhet annihilation at geometric steps.**  Over every commutative ring,
for every `q` and every polynomial of degree strictly below `k`,

`∑_{T ⊆ range k} (-1)^{|T|} p(x + ∑_{j ∈ T} q^j) = 0`.

No hypothesis on `q` is used, so this holds at `q = 0`, at roots of unity, in
positive characteristic and with zero divisors. -/
theorem sum_powerset_geometric_eval_eq_zero_of_degree_lt
    {R : Type*} [CommRing R] (q : R) (k : ℕ) (p : Polynomial R)
    (hdeg : p.degree < (k : WithBot ℕ)) (x : R) :
    ∑ T ∈ (Finset.range k).powerset,
        (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, q ^ j) = 0 := by
  have h := sum_powerset_neg_one_pow_eval_of_degree_lt
    (Finset.range k) (fun j : ℕ => q ^ j) p ?_ x
  · exact h
  · rwa [Finset.card_range]

/-- **The sharp moment at geometric steps.**  At degree exactly `k` the signed
block sum no longer cancels:

`∑_{T ⊆ range k} (-1)^{|T|} (x + ∑_{j ∈ T} q^j)^k = (-1)^k · k! · q^{C(k,2)}`,

independently of the translation `x`.  The steps enter only through their
product, which is the triangular power `q^{C(k,2)}`. -/
theorem sum_powerset_geometric_pow_card
    {R : Type*} [CommRing R] (q : R) (k : ℕ) (x : R) :
    ∑ T ∈ (Finset.range k).powerset,
        (-1 : R) ^ T.card * (x + ∑ j ∈ T, q ^ j) ^ k =
      (-1 : R) ^ k * (k.factorial : R) * q ^ k.choose 2 := by
  classical
  have h := sum_powerset_neg_one_pow_pow_card
    (Finset.range k) (fun j : ℕ => q ^ j) x
  rw [Finset.card_range] at h
  rw [h, prod_range_pow_eq_pow_choose_two]

/-- **Coefficient extraction at geometric steps.**  For every polynomial of
degree at most `k`, the geometric block functional reads off the degree-`k`
coefficient against the explicit constant `(-1)^k k! q^{C(k,2)}`.  The two
theorems above are its extremal cases. -/
theorem sum_powerset_geometric_eval_eq_coeff
    {R : Type*} [CommRing R] (q : R) (k : ℕ) (p : Polynomial R)
    (hdeg : p.natDegree ≤ k) (x : R) :
    ∑ T ∈ (Finset.range k).powerset,
        (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, q ^ j) =
      p.coeff k * ((-1 : R) ^ k * (k.factorial : R) * q ^ k.choose 2) := by
  have h := sum_powerset_neg_one_pow_eval_eq_coeff_card
    (Finset.range k) (fun j : ℕ => q ^ j) p ?_ x
  · rw [Finset.card_range] at h
    rw [h, prod_range_pow_eq_pow_choose_two]
  · rwa [Finset.card_range]

/-- The dyadic case `q = 2`: the classical Prouhet constant
`(-1)^k k! 2^{C(k,2)}`.  Compare `thueMorse_affine_power_sum_self_ring`, which
states the same value with the block indexed by `r < 2^k` rather than by
subsets; the Boolean-cube reindexing between the two is
`sum_powerset_two_pow`. -/
theorem sum_powerset_two_geometric_pow_card
    {R : Type*} [CommRing R] (k : ℕ) (x : R) :
    ∑ T ∈ (Finset.range k).powerset,
        (-1 : R) ^ T.card * (x + ∑ j ∈ T, (2 : R) ^ j) ^ k =
      (-1 : R) ^ k * (k.factorial : R) * (2 : R) ^ k.choose 2 :=
  sum_powerset_geometric_pow_card (2 : R) k x

end Fabius
