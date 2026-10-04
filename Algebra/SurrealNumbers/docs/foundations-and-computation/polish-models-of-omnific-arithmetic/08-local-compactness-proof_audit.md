# Proof audit and dependency map

This document records what the manuscript proves and what its checks do not
certify. It is not an independent referee report.

## Main dependency chain

1. In a discretely ordered group, every element bounded between two ordinary
   integer numerals is an ordinary integer. A divisible subgroup therefore
   contains no nonzero ordinary integer.
2. If an additive subgroup V of a discretely ordered ring misses nonzero
   ordinary integers and has a positive additive order unit u, then uv in V
   forces v = 0. Otherwise u|v| <= Nu would force |v| <= N.
3. Thus v -> uv + V injects V into the additive quotient A/V. Dominance of
   the highest-index coefficient strengthens this to an ordered additive
   direct-sum embedding of all the groups u^j V.
4. A Borel total invariant order restricts to compact subgroups. Haar measure
   and Fubini rule out a nontrivial compact subgroup.
5. The classical principal LCA structure theorem then gives an open real
   identity component C. Second countability makes A/C countable.
6. A Borel invariant order on a finite-dimensional real additive group is a
   real-linear flag order. Its highest real coordinate supplies an order unit.
7. If C is nonzero, Steps 2 and 3 inject uncountable C into countable A/C.
   Hence C = 0, and the presentation is discrete and countable.

## Important distinctions checked in the text

- Discrete arithmetic order does not mean a discrete presentation topology.
- The order is total and multiplication preserves positivity. These are not
  replaced by weaker partial-order assumptions.
- The group topology includes continuous inverse. An arbitrary topology on
  a positive monoid need not have a suitable topological group completion.
- There is no continuity or Borel assumption on the multiplication used in
  the main contradiction. No limit is passed through that multiplication.
- V is only an additive subgroup. It need not be an ideal, convex, or a ring.
  A/V is an additive quotient. The direct-sum theorem is not a polynomial-
  ring evaluation theorem with V as a coefficient ring.
- Real-scalar compatibility of a component order is proved, not assumed.
- The Presburger classification is of pointed topological additive groups,
  not a classification of all orders. Interleaved real and countable scales
  are explicitly distinguished using C and its relative infinitesimal set.
- The Cooper finite-witness lemma needs invariance under every element of
  mG. Invariance under the single standard shift m*1 is insufficient.
- All uses of ordinary moduli and finite integer bounds are external. No
  internal induction scheme is smuggled into the ordered-ring theorem.
- The scalar-regularity theorem drops order compatibility but assumes an
  integral domain. It is separate from the main ordered-ring obstruction.
- Borelness of multiplication is not inferred from the fact that addition
  is continuous. The transported domain examples show genuine failures.
- Set-sized surreal fragments only are used. No Polish topology, Haar
  measure, or power set is applied to a proper class.

## Further consequences and hypotheses

The positive-cone local-compactness threshold d <= 1 concerns cones of the
classified locally compact signed groups. The order has exact Borel rank
two in the uncountable Presburger case. All finite-arity definable relations
are both F-sigma and G-delta, by classical quantifier elimination and the
proved cut analysis. Standard quotient and remainder maps are continuous.

The nonseparable polynomial example removes second countability, not
local compactness. The transported-order example removes Borelness of the
order. No example settling the remaining separable non-locally-compact
problem is asserted.

## Executed checks

The exact arithmetic verification script checks 24,470 finite cases with
rational coefficients and ordinary integers. It tests standard division,
coset-invariant witness selection, polynomial amplification identities,
and lexicographic orders. It has no floating-point dependence.

These finite tests cannot certify Borel regularity, the Haar-measure proof,
all-order quantifier elimination, cardinal inequalities, or all real inputs.
Those conclusions stand or fall with the mathematical arguments and their
classical prerequisites. The LaTeX was compiled, references checked, and the
PDF rendered and visually inspected. No Lean formalization was executed.
