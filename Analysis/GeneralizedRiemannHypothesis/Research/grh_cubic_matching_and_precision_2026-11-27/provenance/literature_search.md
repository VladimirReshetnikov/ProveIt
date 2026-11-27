# Literature and novelty assessment

Date: 27 November 2026. This records a targeted search, not an exhaustive
priority investigation.

## Supplied collection

Pinned ProveIt commit: `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6`.

The source theorem, Article source section, quadratic matching subsection
in `sections/rec.tex`, and equal-precision branch recovery subsections in
`sections/lub.tex` were read. Relevant newer Research reports and the seven
incoming ZIP files were searched for duplicated extensions:

- disjoint-prime-products.zip
- grh_extensions_2026-11-27.zip
- dirichlet-zero-multiplicity-and-reconstruction.zip
- dirichlet_zero_filters.zip
- grh_path_rigidity_2026-11-27.zip
- grh_exact_extensions_2026-11-27.zip
- dirichlet-li-kernels.zip

No exact cubic extremal classification or arbitrary unequal-length field
branch kernel/deletion/budget theorem was found there. This is not an audit
of every proof in the 689-page Article.

## Cubic matching: primary sources consulted

- É. Leducq, *Second weight codewords of generalized Reed–Muller codes*,
  arXiv:1203.5244v3, https://arxiv.org/pdf/1203.5244.
  The exact minimum, second weight, and affine-containment statements needed
  were read directly, including the degree-two and largest-even-degree
  boundary cases. These coding results are established inputs.
- É. Leducq, *A new proof of Delsarte, Goethals and Mac Williams theorem on
  minimal weight codewords of generalized Reed–Muller codes*,
  https://arxiv.org/pdf/1001.2554.
- K. Martin and N. Walji, *Distinguishing finite group characters and refined
  local-global phenomena*, https://arxiv.org/pdf/1607.07586.
  Related irreducible/primitive character-agreement questions; not the
  fixed-mass reducible cubic-packet theorem here.
- N. Walji, *Matching densities for Galois representations*,
  https://arxiv.org/pdf/1501.07343. Related irreducible representation
  matching-density problem; not the exact reducible cubic classification.

Search families included: cubic Dirichlet matching densities; matching
Euler factors for products; integral ternary Fourier uncertainty;
Eisenstein valuation and Reed–Muller codes; reducible finite-group
character agreement; cubic local matching and character packet size.
No precise predecessor to the stated extremal formula and all-equality
classification was located.

## Branch recovery: primary sources consulted

- M. Bhargava, *P-orderings and polynomial functions on arbitrary subsets of
  Dedekind rings* (1997), https://doi.org/10.1515/crll.1997.490.101.
  Classical P-ordering framework and integral-valued interpolation.
- D. Grinberg and F. Petrov, *A greedoid and a matroid inspired by Bhargava's
  p-orderings*, https://arxiv.org/abs/1909.01965 and
  https://doi.org/10.37236/9046. Explicitly includes weighted ultrametric
  greedy selection. The weighted greedy rule is not claimed as new.
- O. Amini, *Logarithmic tree factorials*,
  https://arxiv.org/abs/1611.02142. Related unweighted tree-factorial method.

Search families included weighted P-orderings, unequal branch precision,
ultrametric interpolation, jet recovery, deletion distances, and optimal
recording precision. The claimed contribution is the full unequal-length
formal-series observation kernel and its target-jet, exact-distance, and
recording-budget consequences. It is not the weighted greedy rule itself.

## Source verification consulted

- Andrew Sutherland's MIT verification page for the pinned shorter proof:
  https://math.mit.edu/~drew/shortgrh/ (accessed 27 November 2026).
- Upstream `grh` Git tree at the pinned upstream commit, independently
  compared with the vendored tree. The API response details are retained
  in `upstream_tree_identity.json`.

These external reports were not reproduced by a full local Lean build.

## Appropriate priority language

The results are proved here and extend explicit questions in the supplied
collection. The exact claims were not located in the targeted searches.
Absence from that search does not establish worldwide priority, and the
manuscript makes no such assertion. The new work has undergone independent
agent proof review and exact finite checks, not journal peer review or
machine proof certification.
