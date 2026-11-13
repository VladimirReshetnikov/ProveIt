GOAL-DIRECTED CLOSURE ELIMINATION FOR iPRA
Seven-rule presentation and verified size refinements
Prepared for Vladimir Reshetnikov, November 12, 2026

OPEN FIRST
  ipra_abstraction_and_refinements.pdf
  ipra_abstraction_and_refinements.tex

The .tex file is standalone; all mathematical sections and tables are
included in it. The modular editorial sources are also supplied.

RESULT AND LIMIT
  The new AQE closure rule infers its matrix from the goal by capture-
  avoiding all-occurrence abstraction. With unrestricted crossed BRep,
  Hyp, I0, IS, DE, and witness-selected DI, the resulting seven-rule
  calculus has exactly the native scalar calculus's open consequences.
  The pinned scalar bridge gives whole-domain bi-interpretability and
  equiconsistency with full first-order intuitionistic PRA, with actual
  equality and identity comparison maps.

  This does NOT establish the requested new axiomatization below the
  entire compact checker envelope. The new readable AQE checker has
  1672 tokens / 1818 AST nodes / 7132 normalized bytes, versus its matched
  seven-rule ordinary-QE control at 1590 / 1741 / 6830.

  Separate complete checkers of the INHERITED presentations improve
  the direct-source compact byte record 477 -> 476; the native-validation envelope
  (321,369,596) -> (317,358,594); and the whole-input-validation envelope
  (330,380,621) -> (328,368,616). Coordinates are attained by different
  programs. The compact 244-token and 265-AST records are not surpassed.
  Existing compressed execution wrappers measure (18,19,459); they belong
  to a different source-accounting class, and no record over them is claimed.

  A separate 45-node scalar predecessor composes the incoming 26-node
  factor with the incoming reversed comparison. It improves the current
  46-node term, using only computation, equality, and equation induction.
  It adds or removes no primitive axiom or rule.

CONTENTS
  code/abstraction/   Complete AQE checker, two matched controls,
                      positive/negative certificates, symbolic and CLI tests.
  code/checkers/     Seven smaller complete inherited-presentation
                      checkers, exact controls, contracts, proofs and fixtures.
  mathematics/       New proof sections and exact predecessor AST utility.
  paper/             Modular report sources.
  evidence/          Test receipts, source census, archive identities,
                      independent review and machine-readable claims.
  reference/         Attributed inherited theorem sources and the full
                      pinned artifact Python corpus, authenticated by Git blobs.
  LICENSE.txt        Upstream MIT No Attribution license; also applied here.
  MANIFEST.sha256    Checksums of every delivered file except the manifest.

REPRODUCE
  python3 reproduce.py --manifest-only
  python3 reproduce.py
  python3 reproduce.py --pdf

Reproduction runs in a temporary copy and preserves the original package.
The standard Python library suffices for the checks. Exact metrics use
CPython 3.12.14. PDF compilation additionally needs pdfLaTeX and the standard
TeX packages declared in the source. To compile the standalone source:

  pdflatex ipra_abstraction_and_refinements.tex
  pdflatex ipra_abstraction_and_refinements.tex

EXAMPLE
  python3 code/abstraction/checker.py < code/abstraction/fixtures/aqe_reflexivity.json

Acceptance is process status zero and exactly ACCEPT followed by a newline.
The public AQE driver checks closed theorems; verify() checks explicit open
sequents. No arithmetic evaluator participates in proof acceptance.

PROOF STATUS
  The general results are written mathematical proofs with executable
  checks, not newly compiled Lean/Rocq theorems. The upstream bi-interpretation
  is an explicitly cited dependency and its main source is included.
  Independent review refers to separate analysis in this research run,
  not external human peer review. Finite tests do not replace universal proof.
  No global minimum, new compact token/AST record, or theory-size reduction
  from the predecessor is claimed. No repository mutation was made.

PINNED BASELINE
  https://github.com/VladimirReshetnikov/ProveIt
  Commit 167c76930834c17648fcc2509ab16260da4c727d
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  All 2792 Python artifact instances (1624 distinct Git blobs) and all seven
  incoming archives were included in the source audit. Programs are not
  automatically classified as complete checkers merely because they are small.
