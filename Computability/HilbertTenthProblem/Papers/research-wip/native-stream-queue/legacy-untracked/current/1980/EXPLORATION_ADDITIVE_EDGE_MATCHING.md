# Why additive edge features do not replace ordered program matching

An appealing alternative to convolution routing is to supply one selected
edge per history row and require a sum of nonnegative source/destination
mismatches to vanish. The semantic criterion is exact. Its additive
implementation, however, cannot discard adjacency: sums of features of
individual edges are invariant under permutation, whereas program histories
are ordered.

This note records a sharp, limited obstruction and the remaining mixed
operation. It does not exclude nonlinear encodings or claim a new complete
Diophantine operation count. The checker is
`../verification/explore_additive_edge_matching.py`, with its adjacent JSON
receipt.

## 1. A deterministic three-cycle already separates counts from order

Take the fixed deterministic graph

\[
 e_0:0\to1,\qquad e_1:1\to2,\qquad e_2:2\to0.
\]

For a cyclic selected-edge word `e_0,...,e_(u-1)`, write `s_i` and `d_i`
for its source and destination state codes. The exact mismatch energy is

\[
 \mathcal E=\sum_{i=0}^{u-1}(d_i-s_{i+1})^2,
 \qquad s_u=s_0.
\]

It is nonnegative and vanishes exactly when every destination matches the
next source. In the word `(e_0,e_1,e_2)` the energy is zero. In the word
`(e_0,e_2,e_1)` the energy is six and every adjacent edge pair is wrong.

Nevertheless, the two words have exactly the same multiplicity of every
edge. For every fixed feature map `f:E -> Z^k`, with any fixed number of
coordinates,

\[
 \sum_i f(e_i)
\]

is identical for these words. Flow conservation, every scalar moment of
the source and destination colors, and any other additive collection of
per-edge statistics therefore agree. Both words even have the same initial
edge. Determinism of the graph does not make an unordered certificate prove
that a supplied numerical counter history follows that graph.

This differs from the graph-theoretic statement that a nonnegative integral
flow from one endpoint to another contains some path. Existence of a path
with those endpoints does not place its operations in the order of the
separately supplied counter history.

## 2. The nonnegative mismatch cost is not separable

Suppose one tries to compute a pair cost using only a current-edge feature
and a next-edge feature:

\[
 M(e,f)=A(e)+B(f).
\]

Every such cost has zero rectangular difference. In contrast, for squared
state mismatch,

\[
\begin{split}
 &(d_1-s_1)^2+(d_2-s_2)^2
 -(d_1-s_2)^2-(d_2-s_1)^2\\
 &\hspace{30mm}=-2(d_1-d_2)(s_1-s_2).
\end{split}
\]

This is nonzero whenever both state colors vary. In the three-cycle the
corresponding matrix has a rectangle equal to `-2`. Thus even with free
fixed numerals, this mismatch cannot be compiled as a sum of independent
current and next features. The missing term is genuinely mixed:

\[
 \mathcal E=\sum_i d_i^2+\sum_i s_i^2
               -2\sum_i d_i s_{i+1}.
\]

Precompiling squared colors into an edge's fixed code can address the first
two sums, but not the aligned last sum.

## 3. What remains necessary for a packed implementation

The last sum is an aligned product of neighboring rows. Ordinary integer
multiplication of packed words forms every cross product; it does not
automatically compute the aligned products. For example, the middle
coefficient of `(1+2z)(2+z)` is five, whereas the aligned inner product
`1*2+2*1` is four.

Reversing one word makes a central coefficient equal to the desired inner
product. That correlation identity was already recorded in
`EXPLORATION_FINITE_UNIVERSAL_HISTORY_VERIFIERS.md`; it is not a new saving.
It still requires a certified reversal, the correct coefficient window,
and control of lower-coefficient carries. Supplying an unrelated reverse
word leaves an unsound free witness. At fixed small radix, the raw
correlation coefficients also grow with the unbounded history length.

Another legitimate route is to supply neighboring pairs as row symbols and
test pair compatibility locally. Then overlapping pairs must still agree
on their shared edge, giving a new ordered consistency obligation. The
chosen-edge color construction in `EXPLORATION_CHOSEN_EDGE_COLOR_ROM.md`
addresses such order through convolution; its separately counted twelve-
operation route is not replaced by the additive tests above.

The useful next target is therefore a cheap certified mixed product or a
different ordered-history representation. A proof based only on edge
counts, nonnegative per-edge penalties, or finitely many additive color
moments cannot supply that replacement.

## 4. Exact evidence and boundary

The checker enumerates all six permutations of the three chosen edges:
three cyclic orders have zero energy and three have energy six, while all
six tested scalar moment differences vanish in every case. It verifies the
general rectangular-difference identity symbolically and the concrete
packed-product distinction.

The proof covers every finite family of additive per-edge features, not
just those six moments. It does not cover position-dependent constraints,
nonlinear packed encodings, explicit pair symbols, or supported coefficient
tests. No statement about all possible controller encodings, and no new
universal bound, follows from this scoped obstruction.
