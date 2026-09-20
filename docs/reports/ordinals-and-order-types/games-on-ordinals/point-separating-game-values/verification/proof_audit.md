# Proof audit

This note records the main checking obligations. It is not an independent
referee report or a machine-checked certificate.

## 1. Definitions and conventions

The game lasts beta ordinally ordered turns. Each turn is one open query and
one binary answer. Seeker wins when the intersection of all selected sides has
at most one point; otherwise Hider wins. Empty outcomes favor Seeker.
All ordinal sums and products are ordinary ordinal operations.

The set B_lambda consists of ALL binary functions on lambda. A cylinder C_s
contains ALL extensions of the prefix s. The two topologies are not the product
topology and not the two-sided order topology.

## 2. Seeker's upper bound

For a prefix s of length eta, use the global downset consisting of all smaller
eta-prefixes together with the zero child of s. Its trace on C_s is precisely
C_(s followed by 0). This makes the query globally legal. Each answer fixes
one bit. At limits the actual candidate cylinder is indexed by the union of
all previous prefixes. At lambda its size is one.

## 3. Downward Hider strategy

If the entire left child is inside the queried downset, retain it. Otherwise
there is an excluded left-child point. Every right-child point is larger, so
none can lie in the downset. Retain the right child in the complement.

The tracked prefix length is exactly game time. At every shorter stopping time
at least one coordinate is still free. This is a uniform Hider strategy, not
merely a counterplay chosen after seeing a complete Seeker strategy.

## 4. Compact T1 refinement

The basic sets are D minus F, with D downward closed and F finite. Their finite
intersections have the same form, so their arbitrary unions form a topology.
Cofinite sets are included, giving T1. Any neighborhood of the greatest point
contains a cofinite basic set. An open cover is therefore reduced to covering
finitely many exceptional points, giving compactness.

For infinite lambda, the point with first bit 1 and all later bits 0 has
infinitely many predecessors. Every neighborhood of it contains all but
finitely many of these predecessors. It cannot be separated from the greatest
point, whose neighborhoods are cofinite. Thus the construction is NOT Hausdorff.

## 5. Homogeneous finite extension: the key refinement lemma

Assume a full omega-block of coordinates remains after a prefix s. For any open
U, there are two cases.

- U meets C_s only at points whose next omega bits are all zero. Then the
  cylinder obtained by appending 1 is entirely outside U.
- Otherwise choose x in U whose first 1 in that block is at finite position j.
  A basic neighborhood D minus F of x lies inside U. Appending j+1 zero bits
  to s gives a whole cylinder strictly below x and therefore inside D.
  Refine that cylinder into 2^k subcylinders, where 2^k > |F|. At least one
  misses F and is entirely inside U.

The second case uses only a basic neighborhood of one point of U. It remains
valid when U is an arbitrary union of basic sets and itself has infinitely
many omitted points. All additional prefix lengths here are finite.

## 6. Limit-stage accounting

Write lambda = omega * alpha + n, n finite. During game block xi, the tracked
prefix length is omega * xi + k_r after r finite turns. Every extension is
finite and nonempty, so k_r is finite and strictly increases.

At the end of the omega moves, sup_r k_r = omega, hence the union prefix has
length exactly omega * (xi+1). At a limit delta of blocks, continuity gives
sup_(xi<delta) omega * xi = omega * delta. These are ordinal equalities, not
cardinal approximations.

The intersection of the tracked cylinders is exactly the cylinder of the union
prefix. That prefix extends to all of lambda, so the intersection is nonempty.
No compactness theorem is needed to justify these limit intersections.

## 7. Final finite tail

At time omega * alpha, the surviving full cylinder has exactly 2^n points.
Retaining the larger side of each subsequent query leaves at least 2^(n-r)
points after r <= n turns. If r<n, at least two survive. At earlier stopping
times within an infinite block, infinitely many points still survive.

## 8. Strategy quantifiers and determinacy

A shortest positive-length homogeneous extension exists by the lemma; choose
lexicographically first among the shortest ones. This fixes a rule depending
only on the current prefix and the current open set. No future queries are
used. Set-theoretic strategies need not be effectively computable.

The constructions supply a Hider strategy below lambda and a Seeker strategy
at and above lambda. Thus these particular games are determined. No assertion
of determinacy for arbitrary topological spaces is made.

## 9. Order embedding characterization

A winning downward-query strategy assigns each hidden point its complete
answer word. Encode inside as 0 and outside as 1. Distinct points have distinct
words. At the first differing answer of x<y, downward closure forces the ordered
pattern 0,1, so the code is an order embedding. Conversely pull back the canonical
binary-prefix cuts along an order embedding. No topology on the binary code
space beyond the specified downsets is being silently used.

## 10. Nonadaptive separation calculation

For downward topology, every proper binary prefix determines an adjacent pair
(maximum of its left child, minimum of its right child). One downset separates
at most one such gap; canonical cuts separate all of them.

For the finite-deletion topology, an arbitrary open set splits only countably
many of any ordered family of fibres: an included point in one split fibre has
a basic neighborhood containing all earlier excluded representatives except a
finite deletion. Thus each split fibre has only finitely many earlier split
fibres. Such an ordered set injects into the natural numbers by predecessor
count. This handles arbitrary unions of basic sets.

## 11. What computation establishes

The Python script validates finite minimax counts, all tested ordered cuts,
finite majority bounds, and the finite-hole pigeonhole step. It does NOT prove
transfinite recursion, topology axioms in a proof assistant, or research novelty.

## 12. Scope and outstanding issue

The selected source's Problem 1.2 asks for a topological space in an explicitly
T0 framework. The construction provides an even T1 compact example. It is not a
Hausdorff example. A claim to resolve the Hausdorff spectrum would therefore be
unsupported by these arguments.
