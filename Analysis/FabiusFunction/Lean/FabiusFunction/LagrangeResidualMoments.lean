import FabiusFunction.CompleteHomogeneous
import FabiusFunction.GeometricLagrange

/-!
# All higher residual moments of finite interpolation

This module identifies every moment beyond the exactness range of a finite
evaluation rule.  For a finite node family `v` indexed by `s`, put

`N_s(X) = prod i in s, (X - v i)`

and let `Q_(s,r)(X)` be `completeHomogeneousQuotient s v r`, the polynomial
`h_r(X, (v i)_(i in s))`.  The central polynomial identity is

`X^(#s+r) = N_s * Q_(s,r) + E_(s,r)`,  with  `degree E_(s,r) < #s`.

Consequently `Q_(s,r)` is the quotient of `X^(#s+r)` by the monic nodal
polynomial.  More importantly, any weighted node functional which reproduces
the moments below `#s` also reproduces `E_(s,r)`.  Evaluating the displayed
identity at the target and at the nodes gives the all-order residual formula

`sum_i w_i v_i^(#s+r)
  = x^(#s+r) - prod_i (x - v_i) * h_r(x, (v_i)_i)`.

The generic result needs only a commutative ring and the low-moment
hypothesis: nodes may repeat and no division is used.  Distinctness and a
field enter only in the final corollary which obtains those low moments from
the Lagrange weights.

## Main results

* `degree_lagrangeResidualPolynomial_lt_card` gives the strict degree bound
  for the residual polynomial, including the zero ring and the empty family.
* `X_pow_card_add_divByMonic_nodal` identifies the complete homogeneous
  quotient with Mathlib's quotient by the monic nodal polynomial.
* `sum_weight_mul_pow_card_add` is the representation-independent all-order
  moment theorem for an arbitrary polynomially exact finite row.
* `sum_lagrangeEvalWeight_mul_pow_card_add` specializes it to finite Lagrange
  evaluation at arbitrary distinct field-valued nodes.
* `sum_lagrangeEvalWeight_mul_pow_card_add_zero` removes the distinguished
  zero variable for nonempty evaluation-at-zero rows.
-/

set_option autoImplicit false

open scoped BigOperators Polynomial

namespace Fabius

open Finset Polynomial

noncomputable section

/-- The degree-`< #s` remainder left after removing the complete homogeneous
quotient from the monomial `X ^ (#s + r)`.

This definition makes sense over every commutative ring.  It is zero for the
empty node family, and it is also zero in the trivial ring. -/
def lagrangeResidualPolynomial
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (r : ℕ) : R[X] :=
  Polynomial.X ^ (s.card + r) -
    Lagrange.nodal s v * completeHomogeneousQuotient s v r

/-- The residual polynomial has degree strictly below the number of nodes.

The proof is valid over an arbitrary commutative ring.  In the nontrivial
case it splits off one node and uses the adjoining-node recurrence for
`completeHomogeneousQuotient`; in the trivial ring every polynomial is zero.
No distinctness hypothesis on the node values is needed. -/
theorem degree_lagrangeResidualPolynomial_lt_card
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (r : ℕ) :
    (lagrangeResidualPolynomial s v r).degree <
      (s.card : WithBot ℕ) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    have hzero : lagrangeResidualPolynomial s v r = 0 :=
      Subsingleton.elim _ _
    rw [hzero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · letI := hR
    induction s using Finset.induction_on generalizing r with
    | empty =>
        simp [lagrangeResidualPolynomial]
    | @insert i s hi ih =>
        have hresidual :
            lagrangeResidualPolynomial (insert i s) v r =
              lagrangeResidualPolynomial s v (r + 1) +
                Lagrange.nodal s v *
                  Polynomial.C
                    (completeHomogeneousEvalOn (insert i s) v (r + 1)) := by
          simp only [lagrangeResidualPolynomial,
            Finset.card_insert_of_notMem hi,
            Lagrange.nodal_insert_eq_nodal hi,
            completeHomogeneousQuotient_insert hi v r]
          rw [Nat.add_assoc, Nat.add_comm 1 r]
          ring
        rw [hresidual, Finset.card_insert_of_notMem hi]
        refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (ih (r + 1)).trans
            (WithBot.coe_lt_coe.2 (Nat.lt_succ_self s.card))
        · refine (Polynomial.degree_mul_le _ _).trans_lt ?_
          calc
            (Lagrange.nodal s v).degree +
                (Polynomial.C
                  (completeHomogeneousEvalOn (insert i s) v (r + 1))).degree ≤
                (s.card : WithBot ℕ) + 0 :=
              add_le_add (le_of_eq Lagrange.degree_nodal)
                Polynomial.degree_C_le
            _ = (s.card : WithBot ℕ) := add_zero _
            _ < ((s.card + 1 : ℕ) : WithBot ℕ) :=
              WithBot.coe_lt_coe.2 (Nat.lt_succ_self s.card)

/-- The complete homogeneous polynomial is exactly the quotient of the
corresponding monomial by the monic nodal polynomial. -/
theorem X_pow_card_add_divByMonic_nodal
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (r : ℕ) :
    (Polynomial.X ^ (s.card + r) /ₘ Lagrange.nodal s v) =
      completeHomogeneousQuotient s v r := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact Subsingleton.elim _ _
  · letI := hR
    exact
      (Polynomial.div_modByMonic_unique
        (completeHomogeneousQuotient s v r)
        (lagrangeResidualPolynomial s v r)
        (Lagrange.nodal_monic (s := s) (v := v)) ⟨by
          simp only [lagrangeResidualPolynomial]
          ring,
        by
          simpa only [Lagrange.degree_nodal] using
            degree_lagrangeResidualPolynomial_lt_card s v r⟩).1

/-- The companion remainder identity.  It records that the explicitly
defined residual polynomial is Mathlib's remainder by the nodal polynomial. -/
theorem X_pow_card_add_modByMonic_nodal
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (r : ℕ) :
    (Polynomial.X ^ (s.card + r) %ₘ Lagrange.nodal s v) =
      lagrangeResidualPolynomial s v r := by
  simp only [lagrangeResidualPolynomial,
    Polynomial.modByMonic_eq_sub_mul_div,
    X_pow_card_add_divByMonic_nodal]

/-- Evaluation of the residual polynomial at an arbitrary target. -/
theorem eval_lagrangeResidualPolynomial
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (x : R) (r : ℕ) :
    (lagrangeResidualPolynomial s v r).eval x =
      x ^ (s.card + r) - (∏ i ∈ s, (x - v i)) *
        completeHomogeneousEvalAt s v x r := by
  rw [lagrangeResidualPolynomial, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Lagrange.eval_nodal, eval_completeHomogeneousQuotient]

/-- At every indexed node the nodal factor vanishes, so the residual has the
same value as the original monomial.  Repeated node values are allowed. -/
theorem eval_lagrangeResidualPolynomial_at_node
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (v : ι → R) (r : ℕ)
    {i : ι} (hi : i ∈ s) :
    (lagrangeResidualPolynomial s v r).eval (v i) =
      v i ^ (s.card + r) := by
  rw [lagrangeResidualPolynomial, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Lagrange.eval_nodal_at_node hi, zero_mul, sub_zero]

/-- **All residual moments of a polynomially exact finite row.**

Suppose arbitrary weights reproduce evaluation at `x` in every degree below
the number of indexed nodes.  Then every higher moment has the universal
complete-homogeneous residual shown below.  The nodes need not be distinct;
there is no field or division hypothesis. -/
theorem sum_weight_mul_pow_card_add
    {R ι : Type*} [CommRing R]
    (s : Finset ι) (weight node : ι → R) (x : R)
    (hmoment : ∀ d < s.card,
      ∑ i ∈ s, weight i * node i ^ d = x ^ d)
    (r : ℕ) :
    (∑ i ∈ s, weight i * node i ^ (s.card + r)) =
      x ^ (s.card + r) - (∏ i ∈ s, (x - node i)) *
        completeHomogeneousEvalAt s node x r := by
  calc
    (∑ i ∈ s, weight i * node i ^ (s.card + r)) =
        ∑ i ∈ s, weight i *
          (lagrangeResidualPolynomial s node r).eval (node i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [eval_lagrangeResidualPolynomial_at_node s node r hi]
    _ = (lagrangeResidualPolynomial s node r).eval x :=
      sum_weight_mul_eval_eq_eval_of_moments
        s weight node x s.card hmoment
          (lagrangeResidualPolynomial s node r)
          (degree_lagrangeResidualPolynomial_lt_card s node r)
    _ = x ^ (s.card + r) - (∏ i ∈ s, (x - node i)) *
        completeHomogeneousEvalAt s node x r :=
      eval_lagrangeResidualPolynomial s node x r

/-- **All residual moments of finite Lagrange evaluation.**

For arbitrary distinct field-valued nodes and an arbitrary evaluation point,
the moment of degree `#s + r` differs from evaluation of that monomial by the
nodal product times the complete homogeneous polynomial
`h_r(x, (v i)_(i in s))`.  The formula includes `r = 0`, target points equal
to nodes, and the empty node family. -/
theorem sum_lagrangeEvalWeight_mul_pow_card_add
    {F ι : Type*} [Field F]
    (s : Finset ι) (v : ι → F) (x : F)
    (hvs : Set.InjOn v s) (r : ℕ) :
    (∑ i ∈ s,
      lagrangeEvalWeight s v x i * v i ^ (s.card + r)) =
      x ^ (s.card + r) - (∏ i ∈ s, (x - v i)) *
        completeHomogeneousEvalAt s v x r := by
  exact sum_weight_mul_pow_card_add s
    (lagrangeEvalWeight s v x) v x
    (fun d hd => sum_lagrangeEvalWeight_mul_pow s v x hvs d hd) r

/-- At target zero, every residual moment of a nonempty Lagrange row is the
negative signed nodal product times the complete homogeneous function of the
nodes.  The nonempty hypothesis is exactly what rules out the exceptional
`0 ^ 0` term. -/
theorem sum_lagrangeEvalWeight_mul_pow_card_add_zero
    {F ι : Type*} [Field F]
    (s : Finset ι) (v : ι → F) (hvs : Set.InjOn v s)
    (hs : s.Nonempty) (r : ℕ) :
    (∑ i ∈ s,
      lagrangeEvalWeight s v 0 i * v i ^ (s.card + r)) =
      -(∏ i ∈ s, -v i) * completeHomogeneousEvalOn s v r := by
  have hdegree : s.card + r ≠ 0 :=
    (Nat.add_pos_left (Finset.card_pos.mpr hs) r).ne'
  simpa only [completeHomogeneousEvalAt_zero, zero_pow hdegree,
    zero_sub, neg_mul] using
    sum_lagrangeEvalWeight_mul_pow_card_add s v 0 hvs r

end

end Fabius
