FUSED SCALAR ITERATION FOR iPRA
12 November 2026

RESULT
  A new 46-node scalar predecessor (incoming comparison: 50 nodes),
  a proof that the nine-node three-cycle update is optimal in its specified
  raw syntax, and an exact checker refinement from 267 to 265 AST nodes.

  The requested complete axiomatization below the entire checker-complexity
  envelope HAS NOT BEEN ESTABLISHED. The primitive mathematical rule basis
  is inherited and unchanged. The new checker has 249 tokens / 265 AST nodes /
  605 normalized bytes, so it does not beat the 244-token or 478-byte records.

READ
  ipra_fused_iteration.pdf         Complete report and written proofs
  ipra_fused_iteration.tex         Main LaTeX source
  sections/                       All included report sections
  code/predecessor46.py            Standalone expanded-tree arithmetic utility
  code/clock_minimum.py            Exhaustive exact census through nine nodes
  code/checker_refinement/         New checker, exact control, proof, 10 fixtures
  code/image_scope.py              Independent rejected-substitution calculation
  evidence/                       Receipts, metrics and reproduction outputs
  reference/                      Attributed unmodified upstream proof sources

REPRODUCE
  python3 reproduce.py

The source metrics were obtained with CPython 3.12.14. Other Python versions
can have different AST/unparse conventions. The complete checker modules,
including their reader and fixed ACCEPT output, are measured. The compact
checker has the inherited canonical guarded-goal/integer-list input contract.
It is not a validator for arbitrary hostile JSON.

COMPILE THE PDF
  mkdir -p build
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build ipra_fused_iteration.tex
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build ipra_fused_iteration.tex
  cp build/ipra_fused_iteration.pdf ipra_fused_iteration.pdf

Requires a standard TeX installation with amsmath, lmodern, microtype,
booktabs, enumitem, fancyhdr, listings and hyperref.

PROOF STATUS
The predecessor equations are proved internally using computation, equality
and literal-equation induction. The tests are finite checks and syntax counts;
they do not replace the written proof. No Lean/Rocq verification is claimed.
Bi-interpretability is inherited from the repository's established scalar
bridge and preserved by the proved internal equality of predecessor terms.

SOURCES
Repository: https://github.com/VladimirReshetnikov/ProveIt
Subdirectory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Pinned commit: 017961b8abf22b786f53f29ffdf5a51bdbeaac06
All eleven incoming ZIP archives in that snapshot were inspected and
authenticated against their Git blob identities. See the receipts and
bibliography. No repository mutation was performed.

The 46-node construction and nine-node clock bound are new relative to the
inspected snapshot; no claim of global predecessor minimality is made.
The native core, absorption strategy, codec and arithmetic bridge are
attributed to the existing research packages. Reference sources and the
matched checker control are retained with that attribution.
