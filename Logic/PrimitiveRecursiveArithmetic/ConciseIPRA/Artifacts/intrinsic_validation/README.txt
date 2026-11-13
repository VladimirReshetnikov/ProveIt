INTRINSIC VALIDATION FOR A CONCISE iPRA PRESENTATION
13 November 2026

READ FIRST
  ipra_intrinsic_validation.pdf
  ipra_intrinsic_validation.tex

RESULT AND LIMIT
The complete checker code/checker.py measures 316 significant tokens,
360 Python AST nodes, and 591 normalized UTF-8 bytes (CPython 3.12.14).
This single program is below all three coordinates of the inspected
exact-binding canonical-grammar envelope 321 / 361 / 627.

It is NOT below the compact promised-grammar frontier 239 / 255 / 458
(or 238 / 255 / 455 with the seeded-header convention). No absolute
minimality or new arithmetic axiom basis is claimed. The original global
target remains unmet. This is a complete proof-input refinement of the
existing scalar Choice-DI calculus, whose iPRA bi-interpretation is inherited.

PUBLIC SYNTAX AND TRUST BOUNDARY
The public goal uses genuine bound-variable slots and exactly Eq/D formulas.
JSON true is an explicitly permitted alias for integer code 1, which denotes
numerical zero. Public false is rejected. The predecessor rejected all
Booleans, so the byte-level languages are not identical.

There is no outside promise that the proof payload consists of integers and
lists. The list test and integer bitwise operation validate values when used.
Unused prefix records may be arbitrary JSON; they contribute no assumptions.
Some inert terminal packets need not themselves be lists. The paper gives
the precise successful-run semantics and separates that from tests.

The mathematical theory and its logical macros are fully stated in the
paper. The proof checker does not execute certificate-supplied source and
does not import an external rule table or theorem library.

RUN
  python3 code/checker.py < examples/zero_computation.json
  python3 code/checker.py < examples/induction.json

An accepting process exits normally and prints exactly ACCEPT followed by LF.
Exceptions, resource exhaustion, missing records and all other outcomes reject.
Proof packets are consumed from right to left; the final array element is the
declared goal. The paper specifies the numerical code, scope and mode protocol.

REPRODUCE
  python3 reproduce.py
  python3 tests/verify.py
  python3 reproduce.py --tests
  python3 build_report.py

The exact published metrics use CPython 3.12.14. The measurement program
checks the checksum manifest before measuring. Rebuilding the PDF or changing
any packaged file can change its hash, so verify the original archive first.
The build script uses installed TeX and no network; it can make a private
pdflatex format when system format caches are absent.

VERIFICATION STATUS
The archive includes paper-level soundness/completeness arguments, independent
reviews, regression tests, source metrics and provenance. Tests are evidence
for specified cases, not a proof for every possible input. The inherited
native/iPRA bridge has Lean source; this new Python checker was not formally
verified in Lean or Rocq. Mathematical completeness uses the standard
unbounded finite-call-tree idealization, not finite CPython resource limits.

CONTENTS
  code/checker.py             The single counted trusted program.
  code/checker_readable.py    Uncounted explanatory expansion.
  examples/                  Small accepting and rejecting certificates.
  tests/                     Reproducible focused validation.
  evidence/                  Measurements, reviews, provenance and receipts.
  reference/                 Three exact-binding controls, source references,
                             inherited bridge module and upstream license.
  STATUS.json                Machine-readable scope of the claims.
  MANIFEST.sha256            Integrity hashes for the delivered files.

SOURCE PIN
  https://github.com/VladimirReshetnikov/ProveIt
  fc05b10f0e03f22edbfdde9298a29fb2fee5dc59
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

No remote repository files were modified.
