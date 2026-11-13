A 468-BYTE PRESENTATION OF INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov, 12 November 2026
====================================================================

RESULT AND LIMIT

code/compact468.py is a complete direct-source compact proof checker with
271 significant tokens / 305 AST nodes / 468 normalized UTF-8 bytes.
Its exact matched byte control has 272 / 306 / 469.

The pinned corpus has separate compact records 241 tokens / 262 AST nodes /
469 bytes, attained by different programs. This package improves the byte
record to 468; it does not improve the separate token and AST records.

The change composes existing uniform terminal packets with an existing
two-position coordinate shift. The theory's axioms and inference rules are
unchanged. This is a small implementation refinement, not a new axiom
deletion, a proof of absolute minimality, or a mathematical breakthrough
below every current measure.

OPEN FIRST

ipra_468_presentation.pdf  The complete report: exact rules, preservation
                         proof, arithmetic and logical translations,
                         both interpretation round trips, comparison,
                         verification, and further research questions.
ipra_468_presentation.tex Corresponding main TeX source.

The report uses only code/compact468.py as an external listing. All its
build inputs are included. Files under reference/article are attributed
upstream chapter fragments and are not independent PDF build targets.

TWO EXECUTABLE INTERFACES

code/compact468.py        The exact measured program. It promises a canonical
                         closed guarded Eq/D public goal, final header
                         [goal,0], and exact integer/list certificate data.
                         It does not independently validate those promises.

code/checker_validated.py The recommended standalone entry point for arbitrary
                         JSON input. It validates the complete alphabet,
                         framing, public grammar, genuine/dummy numerical
                         slots, and the atomic guard before running the
                         identical compact inference kernel. This readable
                         companion is 690 / 773 / 2064 after docstring
                         removal and makes no size-record claim.

Both read one finite JSON array as a stack. The final element is [goal,0].
Every consumed preceding instruction has four fields [m,s,u,t]. Unused
integer/list prefixes are allowed. Normal exit with exactly ACCEPT and a
newline is acceptance. Exceptions are rejection. Mathematical completeness
uses ideal finite executions without a fixed machine's resource limit.

Internal proof data need not be canonical. The new trace argument preserves
the inherited theorem for arbitrary internal integer/list trees under the
canonical public-root contract.

PROOF AND INTERPRETATIONS

The new program and the older shifted offset472 program have identical
openers and nonterminal rule bodies. A successful eager no-image opening
fixes the raw input literally. Their successful proof trees therefore
correspond by inserting [0,0,0,0] at hypothesis terminals or deleting the
new terminal packets there. Scope allocation and the public root are
unchanged. This is certificate-existence equivalence, not same-file equality.

The guarded scalar calculus and its full iPRA bi-interpretation are inherited
from the pinned repository. The same arithmetic and logical translations
are retained. Domains are whole, numerical equality is actual, and both
comparison graphs are x=y. No new Lean/Rocq verification of Python is claimed.

The supplement in the main report identifies an unsafe simplification:
the stored tree [B,B,B] can come from opening D B or from introducing a
formula with Q B as its matrix. These require different mode images. If
progression for Q matrices were added while retaining the native gated
logical interface, it would yield induction for arbitrary formulas. No
concrete extra theorem for a modified Python checker is asserted without
a certificate or its compiler theorem.

REPRODUCE

Run from this extracted package directory with Python 3.12.14 for identical
normalization measurements:

  python3 code/verify.py
  python3 code/verify_validated.py
  python3 tests/verify_composition.py code/reference_offset472.py code/compact468.py
  python3 code/checker_validated.py < examples/direct_zero_seed.json

The example proves I(0,0;u.0)=0 and prints ACCEPT.

The first two verification commands write fresh receipts in code/. The
delivered original receipts are kept separately in evidence/. They do not
import or execute untrusted repository sources; the regression runners
execute only the included named checkers in isolated Python processes.

The read-only census utility measures files and archives without executing
their source. Point it at a checkout of the pinned ConciseIPRA directory:

  python3 tests/measure_corpus.py /path/to/ConciseIPRA > census.json

It measures source, not checker soundness. Qualified controls and exclusions
are recorded in evidence/baseline_manifest.json.

To rebuild the PDF, use ordinary pdfLaTeX and the packages in the preamble:

  pdflatex -halt-on-error ipra_468_presentation.tex
  pdflatex -halt-on-error ipra_468_presentation.tex

VERIFICATION

560 isolated compact/control executions: 140 cases, two programs, normal
and optimized Python; zero failed expectations.
264 readable-counterpart executions; zero failed expectations.
346 validated-interface executions: 173 cases, including 33 focused grammar
and alphabet cases, normal and optimized Python; zero failed expectations.
13 independent AST composition checks passed.
The compact and validated inference kernels are AST-identical.

Tests supplement the written proof; they do not establish universal
soundness, completeness, the interpretation theorem, or an absolute minimum.

CONTENTS

code/       Measured, readable, and validated checkers; exact controls;
            translation utility; fixtures; verification runners; proofs.
tests/      Independent structural verifier and read-only corpus census.
examples/   A small complete accepted certificate.
evidence/   Measurements, execution receipts, qualified-source provenance,
            source census, and independent reviews.
reference/  Attributed upstream arithmetic, guard, and checker mathematics.
CLAIMS.json Machine-readable claims and explicit limits.
PROVENANCE.json Source snapshot, comparison identities, and attribution.
MANIFEST.sha256 SHA-256 inventory of the delivered files, excluding itself.
LICENSE.txt Upstream MIT No Attribution license, retained for clarity.

SOURCE SNAPSHOT

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: dd308d5d938b20dce41a1150fa5db49fc53c5d4e
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All nineteen incoming ZIP identities were verified. The audit includes the
current Artifacts Python sources, so the comparison does not rely on the
older main README table. Its observed minima are achieved upper bounds on
an unknown optimum, not mathematical lower bounds.

No changes to the remote repository are part of this deliverable.
