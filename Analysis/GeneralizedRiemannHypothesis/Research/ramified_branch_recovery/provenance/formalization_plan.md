# Formalization plan

This file specifies a possible proof-assistant decomposition. It is a plan,
not a Lean file, a compiled development, or evidence of formal verification.
The upstream GRH theorem is not a logical dependency of these results.

## 1. Finite contact geometry

Input a finite nonempty type of branch labels and a symmetric positive
integer contact on distinct labels, satisfying the ultrametric inequality
`s(a,c) >= min(s(a,b),s(b,c))`. Construct the compact rooted cluster tree.
Handle a singleton directly. Prove that common-path lengths reproduce
contacts and that the construction terminates by strict decrease of cluster
size.

Define greedy marginal costs by finite minimization. The tree merge theorem
can be formalized independently of formal power series: at a node of
incoming length `ell`, the marginal of index `j` is `j*ell` plus the `j`th
entry of the sorted union of child marginal lists. Use finite lists plus an
explicit infinity convention for missing entries.

## 2. Adversarial capacity

Define capacity as the largest size of a retained leaf subset whose
rank-`r` marginal is at least threshold `T`. Quantify over all finite
subsets; the empty subset makes the maximum nonempty.

The key finite theorem identifies a threshold comparison with the number
of child entries strictly below `T-r*ell`. Prove the recurrence by the two
finite optimizations:

1. Any admissible retained set induces child rank budgets with total at
   most `r`.
2. Maximizing child sets for any such budget allocation have an admissible
   union.

The endpoint conventions matter: use strict `<` for counts below a
threshold, allow zero budgets, and give missing entries value infinity.
Backtracking witnesses can be packaged with each maximizing value.
This layer is a suitable first standalone formalization target.

## 3. Valuation and Newton bases

For a field `k`, work over `k[[X]]` and its fraction field. Associate each
label with a distinct branch in `X*k[[X]]`. Prove the contact axioms from
the valuation inequality. Define the monic Newton polynomials and their
nonzero evaluation denominators.

Greediness proves that normalized Newton polynomials are integral-valued
on every branch. Successive evaluation at greedy branches proves the
converse expansion theorem. Identify the possible leading coefficients
with a fractional ideal to prove independence of greedy tie choices.

## 4. Arbitrary two-variable formal series

Implement substitution into a branch and prove continuity for the maximal
ideal filtration. Prove elementary division of `H(X,Y)-H(X,u(X))` by
`Y-u(X)` and iterate to obtain the finite Newton remainder plus a multiple
of the full branch product.

Show that the order of a remainder is the minimum of the coefficient
valuation plus Newton index. The noncancellation proof chooses the largest
index among terms attaining that minimum.

This gives the exact observation kernel and the unresolved-jet dimension.
It also handles arbitrary higher-order terms, which must not be replaced
by an unjustified degree bound.

## 5. Relative distance and errors/erasures

Define block Hamming distance and distinguish target jets from arbitrary
observation words. Prove that the largest zero-block set of a nonzero
target is exactly the capacity at rank `d-1` and threshold `n`.

Prove unique recovery iff `2*t+e < distance`: the forward implication uses
the union of disagreement locations; necessity splits a minimum-distance
pair after erasing some differing locations. For fixed erasures, restrict
the branch family first.

## 6. Saturation and the binary certificate

Use Lagrange interpolation on each `d`-element set to identify its last
factorial with the largest contact row sum. Maximizing those sums proves
the exact saturation formula.

For the sixteen multiplicative branches over F2, establish the contacts
`2^v2(b-c)` and certify the small child-capacity tables by finite reduction.
Combine those tables with the general theorem to prove the exact 15
threshold. The precision-14 product witness supplies the lower bound by
direct finite polynomial evaluation.

## Validation boundary

The included Python computations give useful fixtures for such a
formalization, but importing their output is not a proof. A completed Lean
development must derive the finite certificate by trusted reduction or
prove a verified checker and feed it the certificate, and must connect the
finite tree layer to the power-series algebra and target-jet distance.
