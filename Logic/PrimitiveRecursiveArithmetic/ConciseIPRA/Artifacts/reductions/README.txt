REFINING CONCISE iPRA
A shorter rigidity proof, exact binder-depth bounds, and a checker refinement
Prepared for Vladimir Reshetnikov, November 12, 2026

STATUS
The requested new axiomatization below all current complete-checker records
has NOT been established. This package contains proved partial mathematical
results and a smaller implementation of an existing theory. It does not claim
absolute minimality, a new axiom deletion, or a new Lean/Rocq verification.

START HERE
  ipra_reductions.pdf       Complete report with inherited proof appendices.
  ipra_reductions.tex       Self-contained TeX source; no external input files.
  CLAIMS.json              Exact positive claims and limitations.

NEW MATHEMATICS
1. From successor uniqueness, e(0)=0 and e(S(e(x)))=S(e(x)), define
     r(n)=I(n,0;u.S(e(u))).
   Then e(r(n))=n, r(Sn)=Sn, and e(Sn)=Sn. Consequently the existing
   rigidity argument can omit coverage if e is idempotent, or omit
   idempotence if coverage is retained. This does not yet bootstrap full
   equality reflection or equation induction from successor uniqueness.
2. In the STANDARD CLASSICAL reading of native Eq/D formulas, depth at most
   d defines exactly Sigma^0_(2d) for d>=1; depth zero is exactly PR.
   The constructive lower inclusion was already in the repository. The
   upper bound and strict-depth consequences are the extension here.
   This is a formula-depth theorem, not a Python-source lower bound or an
   intuitionistic prenex-normal-form theorem.

NEW IMPLEMENTATION
Whole normalized standalone module sizes (tokens / AST nodes / UTF-8 bytes):
  checker/control629.py   324 / 374 / 629
  checker/checker621.py   332 / 381 / 621
  checker/checker620.py   337 / 385 / 620

These modules validate the PUBLIC CLOSED NATIVE Eq/D GOAL. The mathematical
correctness statement retains the finite exact-integer/list proof-data
contract. They do NOT validate every value in the whole JSON certificate;
unused prefixes are inert. The complete simulation argument is in the paper
and checker/PROOF.txt, including contexts modulo duplicate zero entries.

The current COMPACT records are 248 tokens / 270 AST nodes / 487 bytes,
in DIFFERENT programs. They assume a canonical guarded public goal and do
not independently validate its grammar. The first two use first-line JSON
framing; the byte program uses multiline JSON. Those three record sources
are included under baseline/. The new checker does not beat that envelope.

THEORY AND INTERPRETATIONS
The inherited scalar native theory and its ordinary realization remain
bi-interpretable and equiconsistent with full first-order iPRA. The report
states every native rule and both interpretations; whole numerical domains,
actual equality, and identity comparison graphs x=y are preserved.
The new implementation has the same finite integer/list acceptance relation
as the pinned current native control, under sufficient resources.

RUN
  python3 reproduce.py
  python3 checker/checker620.py < checker/fixtures/computation_zero_local.json

Acceptance is normal exit with exactly ACCEPT and one newline. Exceptions
reject. The suite contains 37 fixtures run against three programs in normal
and optimized Python: 222 executions, zero recorded failures. It includes
the known 17-packet future-scope attack. Finite execution supports the
simulation proof; it is not a substitute for a universal soundness proof.

PDF
  python3 build_pdf.py
or
  pdflatex ipra_reductions.tex
  pdflatex ipra_reductions.tex

build_pdf.py first tries installed pdfLaTeX and can create a private format
from installed TeX files if needed. No downloads or global changes are made.
The editable modular sources are under sections/; assemble.py regenerates
the single TeX source. Rebuilding the PDF can legitimately change its bytes
and the build receipt. Verify the delivered manifest before rebuilding.
Use --skip-manifest only for deliberate local changes after verification.

PROVENANCE
  Repository: https://github.com/VladimirReshetnikov/ProveIt
  Revision: ecae4653f69184a25ade2b1aeaa346f7a7817b78
  Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All nine current incoming ZIPs were read and authenticated by Git blob hash.
The filed Python census covers 2,487 parsed source paths / 1,313 distinct
sources, with three parse-failure records kept separately. No repository file
was modified. PROVENANCE.json and evidence/ retain the relevant receipts.
The optional finite-axiom appendix is an application of known interpretability
results; it does not rule out the schematic presentations allowed by the task.

CONTENTS
  checker/     New/control acceptance modules, proof, fixtures, verifier.
  baseline/    The three current compact record sources, for comparison.
  sections/    Editable report components.
  reference/   Attributed inherited arithmetic and protocol proofs.
  evidence/    Source census, incoming identities, PDF build/visual checks.

Inherited material retains the accompanying upstream MIT-0 license. New code
and text may be used under the same terms. Further research questions are
included in the report.
