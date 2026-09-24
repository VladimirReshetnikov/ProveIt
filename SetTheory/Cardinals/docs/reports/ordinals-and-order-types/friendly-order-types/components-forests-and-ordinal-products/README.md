# Friendly Order Types of Finite Posets and Ordinal Products

Incomparability components, forest certificates, and exact transfinite formulas.

Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Provenance

This report merges two independently produced research reports on the same
invariant, originally delivered as the directories
`cartesian-products-of-ordinals` and `incomparability-components-and-forests`.
The first developed the transfinite side (ordinal-cut projection lemma,
finite-tail and upper-tail lemmas, the mixed ordinal-finite product theorem,
the ordinal-box classification, the (o,h,w,f) counterexample). The second
developed the finite side (protected-root deletion lemma, maximum friendly
subsets, spanning-forest certificates and the graphic-matroid reading,
substitution and disjoint-union laws, the enumerative generating function,
the infinite graph-only obstruction).

Both reports independently proved the shared core theorem f(P) = |P| - c(P),
and both proved it by the *same* argument: the same ordered-component lemma,
the same maximal non-cut vertex lemma with the same two-case proof, the same
capacity upper bound, the same top-down assembly. That argument therefore
appears exactly once in the merged article (Section 3), keeping the second
report's protected-root strengthening, which the subset classification needs.

Where the two reports genuinely differed, both proofs are kept: the finite
Cartesian-product formula is proved twice, once by the ordinal-cut projection
route (Section 5.1-5.2) and once by the chain-grid spanning-subgraph route
(Section 5.3, "A second, graph-theoretic proof").

## Main results

Write f(P) for Vialard's friendly order type: the rank of the bad-sequence
subtree in which every selected point has an incomparable friend in the
current residual.

1. For every finite poset P, f(P) = |P| - c(P), where c(P) counts connected
   components of its incomparability graph Inc(P), including isolated
   vertices. Equivalently, f(P) is the rank of the graphic matroid of Inc(P):
   the maximum number of edges in a forest. In particular f(P^op) = f(P).
2. The maximum friendly subsets are exactly the complements of one minimal
   element per incomparability component; their number is the product of the
   counts of those minimal elements. The constructed witnesses carry
   spanning-forest certificates that a verifier checks independently.
3. A Cartesian product with at least two non-singleton factors has exactly
   one non-endpoint incomparability component; existing least and greatest
   points are the only other components. Hence
   f(A x B) = |A||B| - 1 - eps_bot(A)eps_bot(B) - eps_top(A)eps_top(B),
   proved twice by two independent routes. For the Boolean lattice,
   f(B_d) = 2^d - 3.
4. Arbitrary lexicographic substitution with nonempty finite fibers has an
   exact formula; so do finite ordinal sums and finite disjoint unions.
5. No function of the four invariants (o,h,w,f) of each factor determines
   f(A x B) for general wpos. Explicit four-point factors D and E both
   have tuple (4,3,2,1), but f(D x 2) = 5 and f(E x 2) = 6. Already on three
   elements, (|P|,o,h,w) fails to determine f, and the gap can be as large
   as n-2.
6. Let P = alpha_1 x ... x alpha_r x B, with r >= 1, each alpha_i infinite,
   B finite nonempty, and r >= 2 or |B| >= 2. Its friendly order type is
   Theta = alpha_1 natural-product ... natural-product alpha_r
   natural-product |B|, except that it is the right predecessor of Theta
   when every alpha_i is a successor and B has a greatest element.
7. This gives a complete classification for finite Cartesian products of
   ordinals, including empty factors, singleton factors, and finite boxes.
8. The friendly order type of a well-ordered sum is the ordinal sum of the
   summands' friendly order types. Consequently every ordinal alpha is
   realized, by a sum of alpha two-element antichains, at ordinary antichain
   width two - although all countably infinite such posets have isomorphic
   incomparability graphs. So on infinite wpos the graph alone no longer
   determines the invariant, and the finite matroid reading does not extend.
9. An exact bivariate generating function counts naturally labelled posets by
   friendly rank: A(z) = 1/(1-B(z)) and sum a_{n,k} z^n u^k =
   1/(1 - sum_m b_m z^m u^{m-1}), with fixed-rank counting polynomials.

## Status

The broad compositional computation of friendly order type is identified as
an open research direction in Vialard's MFCS 2023 paper and 2024 thesis.
The exact restricted questions in this report are our formulations within
that direction; we do not claim the literature labels the finite statement as
a named conjecture. The invariant itself, the multiset-width transfer, the
both-limit product case and the binary ordinal-sum formula are Vialard's and
are not claimed as new. The finite disjoint-union identity is consistent with
published finite formulas and is not claimed as a new special case.

Conventional proofs are supplied. The transfinite theorem explicitly uses
published maximal-linearization/natural-product results and Vialard's
limit-saturation corollary. The exact new-to-this-report formulas were not
located in the checked sources, but publication priority has not been
certified, and the elementary ingredients may be known in other terminology.
The arguments are presented as proofs; the manuscript has not been
independently refereed, formally verified, or checked by a proof assistant.
This is not a peer-reviewed paper or a Lean formalization. It does not solve
the unrestricted general compositional program.

## Contents

- `friendly_order_types.pdf`: compiled article.
- `friendly_order_types.tex`: self-contained LaTeX source with an inline
  bibliography (no BibTeX pass is required).
- `build.sh`: PDF build helper.
- `code/friendly.py`: finite-poset engine - graph formula, independent
  residual dynamic program, protected-root non-cut construction, optimal
  certificates with spanning-forest roots, certificate verifier,
  lexicographic substitution, duals, ideal-based enumeration of naturally
  labelled orders.
- `code/friendly_cli.py`: command-line front end for a single JSON input.
- `code/finite_posets.py`: the second, independent finite-poset
  representation - own validation, own residual-tree rank, graph formula,
  search-based constructive certificates, products, height, width, covers,
  and its own exhaustive naturally labelled enumeration.
- `code/ordinal_cnf.py`: exact hereditary Cantor normal forms below epsilon_0;
  ordinary addition, natural sum/product, predecessor, formula evaluators.
- `code/verify.py`: reproducible tests; Python standard library only.
- `code/check_distribution.py`: checks the A = 1/(1-B) convolution against
  the saved rank distribution.
- `examples/diamond.json`, `examples/chain_plus_isolate.json`,
  `examples/N_poset.json`, `examples/empty.json`: concrete inputs given by
  strict generating relations.
- `data/verification_results.json`: top-level scope and counts of all checks.
- `data/finite_verification.json`, `data/finite_verification.txt`: the
  exhaustive naturally labelled run through size seven, with per-size rank
  histograms and the sub-check counts.
- `data/rank_distribution.csv`: exact counts by support size and friendly
  rank, n = 0..7.
- `data/generating_function_check.json`: the A = 1/(1-B) consistency check
  and the connected counts b_1..b_7.
- `data/examples_results.json`: computed friendly order type, DP value,
  components and certificates for the four shipped examples.
- `data/counterexample_certificate.json`: exact relations, covers, invariants,
  incomparability components, moves, friends, and residuals.
- `data/ordinal_examples.json`: exact symbolic ordinal-box examples.
- `PROOF_DEPENDENCIES.md`: dependency map.
- `RESEARCH_STATUS.md`: literature, scope, and verification boundaries.

## Calculate a finite example

Python 3.10+ is required. From this directory:

```sh
python3 code/friendly_cli.py examples/diamond.json --dp
python3 code/friendly_cli.py examples/chain_plus_isolate.json --dp
python3 code/friendly_cli.py examples/N_poset.json --dp
python3 code/friendly_cli.py examples/empty.json --dp
```

The two four-element examples `diamond.json` and `chain_plus_isolate.json`
have the same cardinality, height and ordinary width, but friendly ranks
1 and 3. Their multiset ordinal widths are omega and omega^3.

Input format:

```json
{"n":4,"relations":[[0,1],[0,2],[1,3],[2,3]]}
```

Labels are integers 0 through n-1. Relations are *strict generating*
relations (Hasse edges are acceptable); the program takes transitive closure.
Cycles and out-of-range labels are rejected. Labels need not be a linear
extension. With no `relations`, the input is an antichain.

Optional `"roots":[...]` requests specific roots: provide exactly one root
per incomparability component, each minimal within its own component.
For example, the diamond accepts `"roots":[0,2,3]` and returns a sequence
using only vertex 1. A root of a later component can be removed when an
earlier component is processed; it remains a root of the certificate forest,
not necessarily an element of the final residual.

`--dp` requests the independent exponential reference computation. Avoid it
for large posets: the formula itself is quadratic on a comparison matrix,
but the reference recursion may visit up to 2^n subsets.

## Reproduce computations

From this directory:

```sh
python3 code/verify.py
python3 code/check_distribution.py
```

The first command rewrites the data files listed above. It needs no network
access, Wolfram kernel, SageMath, or external Python packages. Explicit
checks are not disabled by Python's `-O` option. Use `--max-n` to change the
exhaustive bound and `--out` to write the reports elsewhere; a quick smoke
test is `python3 code/verify.py --max-n 4 --out /tmp/friendly-check`, which
still runs the composition and maximum-subset checks over their documented
fixed ranges.

Completed checks in the delivered run (Python 3.14.4, 40.685 s):

- 101,660 naturally labelled posets of sizes 0 through 7; for each, the
  direct residual rank equals the component formula, the dual order gives
  the same rank, and an optimal certificate is constructed and simulated
  with its spanning forest verified.
- 90,655 connected-case maximal non-cut checks.
- 2,601 Cartesian-product pairs over factor sizes 0 to 4, supports up to 16,
  with both the graph count and the independent residual recursion; on the
  2,401 pairs with both factors of size at least two, the unique
  non-endpoint incomparability component was also checked.
- 10,725 heterogeneous lexicographic substitutions.
- 2,365 candidate maximum friendly subsets through support size five,
  including 1,052 prescribed-root certificates.
- 8 malformed orders or malformed friend claims, all rejected.
- The A = 1/(1-B) convolution reproduces every rank histogram.
- A cross-implementation re-derivation by the independent `FinitePoset`
  engine, with its own constructive certificates, on all 5,231 nonempty
  orders through size six plus the empty poset. This is a second-engine
  check over a smaller range, not a second exhaustive-enumeration figure.
- The four-point-factor counterexample, including equal ordinary product
  invariants (8,4,3) and different friendly types 5 and 6; the three-element
  separation; and the extremal L_n / R_n families for n = 3..7.
- 387 finite-surrogate corner-strategy cases, including two no-move cases.
- 7,200 sampled ordinal-algebra identities and six worked box examples,
  plus finite arithmetic, predecessor, and degeneracy checks.

Naturally labelled enumeration is not enumeration of every relabelling
and is not an isomorphism quotient. Every isomorphism class through the
stated size has a representative in this enumeration, generally several.

## What the computations do not establish

The direct finite rank algorithm is independent of the component formula,
but testing finitely many inputs is not the general proof, and it verifies
no transfinite theorem. Corner simulations replace limit cutoffs by 2 and
test only legal moves, witnesses, move counts, and residuals. They do not
verify transfinite rank. The ordinal evaluator implements the proved formula;
it is not an independent infinite-tree rank oracle. Its notation system
excludes epsilon_0 and omega_1, even though the mathematical theorem permits
arbitrary set-sized ordinals. The generating-function script is a consistency
check on saved counts, not an independent enumeration. Certificates are
algorithmically verified, but the English proofs have not been formalized or
externally refereed.

## Build the PDF

A standard TeX installation providing the packages in the preamble is
required, including New PX, amsmath, amsthm, mathtools, microtype, TikZ,
tcolorbox, listings, hyperref, and booktabs. No BibTeX pass is needed: the
article carries its bibliography inline.

```sh
sh build.sh
```

Temporary LaTeX files are put in `.latex-build/`. The resulting PDF is
copied into this directory. No font files are included in the archive.
