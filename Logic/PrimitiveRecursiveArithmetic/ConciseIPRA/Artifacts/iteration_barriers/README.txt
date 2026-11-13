iPRA: ITERATION BARRIERS AND AN AUDITED BASELINE
Prepared for Vladimir Reshetnikov - 12 November 2026

STATUS
The requested below-frontier axiomatization has NOT been obtained.
No new smallest checker, globally minimal theory, or successful size reduction
is claimed. The report contains rigorous mathematical obstructions to two
possible reductions, a precise positive equivalence, and reproducible baseline
measurements. Read report.pdf or compile report.tex.

MAIN FINDINGS
1. Induction for equations against every fixed standard numeral remains too
   weak even after adding identity iteration, all standard-seed successor
   numbering laws (including I(n,0;u.Su)=n), and body extensionality.
2. Iterator fusion remains too weak without the numbering law. A concrete
   model validates fusion but refutes that law.
3. Automorphisms of these models obstruct the specified bi-interpretations;
   the precise parameter qualifications are stated in the report.
4. Fusion plus the numbering law recovers the existing arbitrary-update
   uniqueness rule UR. Its known bootstrap gives equivalence to equation
   induction; this is not a smaller presentation.

BASELINE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1156099ffe30f7497d2c11ab20271f46cffcd115
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Whole-input observed coordinate envelope: 248 tokens / 268 AST nodes /
469 normalized bytes, attained by THREE DIFFERENT programs.
Allowing JSON-line streams: 242 / 262 / 469, again three programs.
The supplied checkers are unchanged attributed upstream programs.

REPRODUCE
  python3 audit/reproduce_frontier.py
  python3 audit/reproduce_whole_json.py
  python3 reproduce.py
  python3 reproduce.py --pdf

The Python checks use only the standard library and no network. Metrics match
CPython 3.12.14; ast.unparse output can change with another version. Gzip uses
level 9 and mtime=0. PDF rebuilding uses build_pdf.py and requires pdflatex and
the TeX packages named in report.tex. The helper can create a private format
from installed TeX sources, without downloads or global changes. Rebuilding
updates receipts, so run it in a copy if preserving
the original receipt hashes matters.

EVIDENCE AND LIMITS
Two independent suites recorded 236 checker-process executions (124 + 112),
with zero failed expectations. One also verified 25 exact upstream Git blob
identities. These tests concern inherited checkers and input framing. They do
not mechanically verify the infinite countermodels or prove Python soundness.
The new mathematical arguments are written proofs, independently reviewed
within this work; no new Lean or Rocq formalization is supplied.

FILES
report.tex, report.pdf          Main self-contained research report.
CLAIMS.json                    Precise status and theorem boundaries.
audit/                         Reproduction scripts and full receipts.
build_pdf.py                   Offline-capable three-pass PDF builder.
baseline/                      Selected upstream sources, controls, fixtures.
reference/                     Pinned chapter extracts and source metadata.
research/                      Detailed proof notes and independent review.
MANIFEST.sha256                Hashes of delivered files.
LICENSE.txt                    License and upstream attribution.

No remote repository change was made.
