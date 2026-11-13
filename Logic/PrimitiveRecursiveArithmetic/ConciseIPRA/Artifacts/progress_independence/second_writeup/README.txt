A LIMIT ON SIMPLIFYING iPRA
Independence of the native progress rule
November 12, 2026

STATUS

This delivery does not establish the requested smaller axiomatization or
a new complete-checker size record. It does establish a written solution
of Further question 1 in the pinned ConciseIPRA README: QI by progress is
independent of the other seven native kernel rule families.

The separating formula is Q_y (I(y,0;u.u)=0). The full kernel has a
six-node proof tree for it; the seven-rule deletion has a countermodel.
The countermodel supports every finite-depth scalar iterator, actual
equality, the whole domain, and step-function extensionality. It may be
chosen countable. The new infinite-model theorem is not Lean/Rocq verified.

START HERE

ipra_progress_independence.pdf   Complete report and proofs.
ipra_progress_independence.tex   Standalone editable LaTeX source.
CLAIMS.json                    Precise positive and negative claim boundaries.

REPRODUCE

  python3 verify.py
  python3 reference/native_eight.py < evidence/progress_witness.json
  python3 build_pdf.py

The measurement convention is CPython 3.12.14, actual docstrings removed,
ast.unparse normalization, one final LF. The three pinned compact profiles
have (significant tokens, AST nodes, normalized bytes):

  frontier_tokens.py: (256, 283, 593)
  frontier_ast.py:    (263, 276, 580)
  frontier_bytes.py:  (267, 303, 506)

The coordinate envelope (256, 276, 506) comes from different programs.
Their compact interface assumes a canonical guarded public goal. It is
not interchangeable with a contract requiring validation of arbitrary
JSON public goals. These are observed records, not proven lower bounds.

The positive witness, its open progress step, and its zero base are
checked independently by an unchanged strict eight-rule native checker.
Both ordinary and optimized Python CLI runs must print ACCEPT and exit
zero. The step contains no QI. Finite execution verifies these positive
certificates and measurements, not the mathematical non-derivability.

CONTENTS AND PROVENANCE

reference/                 Unchanged attributed comparison sources.
reference/foundations/     Relevant inherited arithmetic bridge TeX sources.
evidence/                  Positive certificates and verification receipt.
census/                    Metrics for all 5,825 Python files, the census
                           script, and manual review of small candidates.
SOURCE_PROVENANCE.json     Pinned revision, paths, source hashes and references.
MANIFEST.sha256            Hash ledger of the delivered files.

Pinned repository:
  https://github.com/VladimirReshetnikov/ProveIt
  5c6c2d8d68da11f89cf2937cf7aca3b85805fd41
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The Lean files in reference/ are frozen source references, not a newly
compiled Lean project. The main new proof is in the report. No repository
files were modified or published. The inherited MIT-0 license is retained
in reference/LICENSE_ProveIt.txt; new package materials use the same terms.

The report includes Further research questions. No literature-wide
priority claim or global minimality claim is made.

APPENDIX: STATIONARITY

The report also proves that the rule f(Sz)=f(z) / f(t)=f(0), with no
induction hypothesis, recovers quantifier-free induction over the explicit
interface of PR definitions, coverage, separation, and PR Boolean truth
flags. The interface is iPRA-provable, so this presentation has an identity
domain interpretation back and forth. Deriving that interface from the
stationarity rule in the bare scalar language remains unproved here; no
new small native checker is claimed for it.
