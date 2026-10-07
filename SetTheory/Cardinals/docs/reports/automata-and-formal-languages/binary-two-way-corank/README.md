Binary Two-Way Automata and Corank Budgets in Brauer Monoids
Research article prepared with ChatGPT for Vladimir Reshetnikov
7 October 2026

ENTRY POINTS

  article.pdf     Complete article, proofs, source review, and research agenda.
  article.tex     Main LaTeX file; inputs the seven files in sections/.
  references.bib Bibliography with pinned repository links.

MAIN RESULT

For each h >= 2 the article constructs a completely defined binary language
B_h with a (6h+2)-state one-way nondeterministic finite automaton. Every
equivalent s-state two-way deterministic automaton satisfies

  8s+2 >= 2 (5/2)^floor((h-2)/9).

For each n >= 14, padding the source gives

  s >= (1/4)(5/2)^floor((n-14)/54) - 1/4.

The exponent coefficient is log_2(5/2)/54 = 0.0244801499...
The exact recurrence gives stronger finite bounds; see certificates/
finite_bounds.csv. For instance, source counts 602 and 1202 give target
state lower bounds 8307 and 221212481 respectively.

The machine has two distinct endmarkers, a single initial state at the left
marker, partial transition rules, and moves -1,0,+1. A finite run entering an
accepting state succeeds, including initial acceptance; infinite nonaccepting
runs reject. All states are counted. The source has no left moves.

CONTRIBUTIONS AND ATTRIBUTION

The central proved estimate is that any word in designated Brauer idempotents
has corank at most the sum of those generators' coranks, counted once each
regardless of repetitions. The article uses this budget twice to strengthen
the relation-addition amplifier, proves a symbol-local representation of a
binary s-state 2DFA in degree at most 8s+2, and gives a 2h-state four-letter
relation compiler with a 6h+2-state binary decoder including marker states.

The colored component classification is classical. The relation-corner and
tree-contour architectures are adapted from the OpenAI September 2026
liveness manuscript, with explicit attribution. Linear-size fixed-alphabet
transfer itself has an earlier construction in TheoremDB R816 and is credited.
No global priority certification is claimed.

The determinization theorem is proved self-containedly in the article.
The separate nondeterministic complementation consequence imports exactly
the order-reversing path-diagram image theorem stated in Section 5.
No new Lean formalization or independent human peer review is asserted.
No uniform logarithmic-space separation is claimed.

BUILD

Requirements: a standard TeX Live or compatible LaTeX installation with
pdflatex, bibtex, amsmath, amsthm, mathtools, lmodern, microtype, booktabs,
longtable, array, enumitem, xcolor, tikz, fancyhdr, xurl, hyperref, cleveref.

From this directory:

  make

Equivalently:

  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  bibtex article
  pdflatex -interaction=nonstopmode -halt-on-error article.tex
  pdflatex -interaction=nonstopmode -halt-on-error article.tex

No network or shell escape is needed. The included article.bbl permits
compilation without rerunning BibTeX when the bibliography is unchanged.

REPRODUCE THE FINITE AUDITS

Requirements: Python 3.10 or newer, standard library only.

  python3 code/run_all.py --output-dir reproduced

This executes all mathematical checks with Python optimization enabled.
The scripts use explicit exceptions; optimization cannot disable checks.
The reference run used Python 3.12.14 and took about 98 seconds in the
preparation environment. Runtime is machine dependent.

The runner covers:
  * 146600 perfect matchings through degree seven.
  * Complete two-idempotent-generated monoids through degree four and
    reproducible larger-degree samples of words and corner powers.
  * 365908 exact relation/compiler/decoder cases.
  * 50400 direct-machine versus local-matching comparisons.
  * Exact finite bounds through h=256 and the four-label union obstruction.

Reference outputs are in certificates/. Timing and absolute output-path fields
may differ on rerun. Mathematical counts and the compiler case-stream SHA256
digest must agree. The finite audits are diagnostics; the infinite theorems
are proved in the article.

FILE MAP

  sections/introduction.tex   Problem, reviewed sources, main theorem, scope.
  sections/algebra.tex        Budget, sharp support, corners, full amplifier.
  sections/machines.tex       Sparse local matching construction, optimal order.
  sections/compiler.tex       Four-letter code, decoder, quotient, main proof.
  sections/complement.tex     Explicit external premise and binary consequence.
  sections/verification.tex   Audit design, exact counts, reproducibility.
  sections/research.tex       Further questions, beta bounds, union obstruction.
  code/                      Five audit programs plus their runner.
  certificates/              Executed JSON and exact recurrence CSV.
  SOURCE_AUDIT.txt           Source versions, paths, identities, and limits.
  source_manifest.json       Machine-readable local source snapshot hashes.
  THEOREM_LEDGER.csv         Claim-to-proof and dependency map.
  THIRD_PARTY_NOTICES.txt    Attribution for adapted upstream material.
  LICENSE-APACHE-2.0.txt      License text supplied with the upstream source.
  SHA256SUMS                 Digests of the distributed files, excluding itself.

SUGGESTED PROVEIT PLACEMENT

  SetTheory/Cardinals/docs/reports/automata-and-formal-languages/
    binary-two-way-corank/

This is a proposed directory following the reviewed collection's organization.
No change has been pushed to ProveIt. Keep the relative sections/, code/, and
certificates/ directories when importing. Preserve the source audit, theorem
ledger, and notices so that readers can distinguish the proved extensions,
classical ingredients, and the imported complementation premise.
