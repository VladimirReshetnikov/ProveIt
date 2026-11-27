# Lean formalization plan (not compiled)

This is a dependency design, not a claim of a completed Lean formalization. The mathematical proof is in `prime_routing.tex`. Lean and Mathlib were not installed in the working container.

## 1. Input boundary

In the vendored readable package, the following is the intended import and interface (copied theorem names from `Main.lean`; this snippet was not run):

```lean
import Main

example : DirichletLNonvanishingRightOfHalf :=
  LFunction_ne_zero_of_half_lt_re

example : DirichletLZerosOnLine := LFunction_eq_zero_re
```

Use the vendor's own toolchain, not the root ProveIt package. Upstream axioms are audited by `lake env lean scripts/PrintAxioms.lean`. A full integration should also print the new routing theorem's axioms.

## 2. Finite core, independent of GRH

Suggested definitions (pseudocode, not Lean syntax commitments):

- A finite abelian group `G`, finite set `P` of distinct generators.
- A retained arc predicate `H : G → G → Prop`, where the second argument is the generator label, not the destination. `H x p` means `x → x*p` is permitted. Incoming labels at `x` satisfy `H (x*p⁻¹) p`.
- A witness path is a start vertex and a finite list of labels. Use a scan to compute its vertices; a predicate asserts all its transitions are retained. Require label-list nodup and optionally vertex-list nodup. Avoidance conditions are simple membership predicates.
- Define `bias Q` as the maximum norm of the normalized sum over nontrivial characters, and a finite normalized adjacency operator. Prove the directed mixing inequality from character orthogonality and centred indicator norms.

Lemmas in dependency order:

1. Hoeffding bound for independent signs via a finite product probability space; alternatively use a separate finite discrepancy hypothesis and postpone probability.
2. Simultaneous split: at most `4*n` linear forms; union bound; principal character controls pool sizes; nonprincipal coefficients and degree subsets give the three inequalities.
3. Reachability step with one stored witness for each attained endpoint: forbid used labels, global labels, forbidden vertices. Distinct generator elements ensure forbidden vertices remove at most their cardinality of arcs. Prove `remaining ≥ (1/2+δ/2)*dPool` by casts and linear arithmetic.
4. Directed mixing implies `card U_next ≥ R * card U` while `2*card U_next ≤ n`. Prove by induction that `R^k > n/2` forces a set with more than half the vertices.
5. Repeat with inverses and reversed paths; cardinality pigeonhole gives a common endpoint. Disjoint pools give nodup on the concatenated label list. Erase closed subwalks by well-founded induction on list length.
6. Greedy linkage by induction on number of terminal pairs. Maintain that prior paths avoid every unused terminal, their vertices are pairwise disjoint, and their labels are pairwise disjoint. The forbidden sets have combined size at most `(4*k+2)*r`.
7. Counting obstruction: `≤ ∑_{i<h} d^i` reachable vertices, choose pairs successively, and count globally distinct labels.

The finite theorem can first be proved with the hypotheses of Theorem 3.1 written as inequalities for positive reals and natural `k,B`, including `R^k > n/2`, avoiding logs in the induction. The exact formula for `k` is then a corollary. The probabilistic split can be factored out, so the deterministic routing core is independently reusable and testable.

## 3. Analytic specialization

Needed analytic lemmas (not checked for existing exact Mathlib counterparts): uniform nonprincipal sharp prime-character estimate, integrated prime-power estimate, PNT, imprimitive correction, and elementary totient asymptotics. The first two follow classically from the explicit formula and the exported GRH. At `y=(log q)^A`, the normalized bias is at most `L^(1-A/2+o(1))`; at `y=C*L^2` it can be made as small as a fixed margin. These are classical imported results in the paper, not Lean theorems produced in this session.

Finally instantiate `G` with the unit group of `ZMod q`, labels with small primes not dividing `q`, and injectivity using `p<q`. Show all finite inequalities for sufficiently large `q`. Keep the graph theorem separate from the arithmetic specialization; do not introduce an axiom named GRH when linking to the actual vendored proof.
