A SUBSTITUTION-STABLE SEVEN-RULE PRESENTATION OF iPRA
Research construction, November 11, 2026

MAIN DELIVERABLES
  ipra_diagonal_guard.pdf   Complete report and inherited arithmetic proofs
  ipra_diagonal_guard.tex   Self-contained LaTeX source (no external inputs)

RESULT
Keep the complete original scalar term language and Eq/Q/D formula language.
Replace case DI and equation-progress QI by one D-introduction:

  Gamma, B(t, eta(z)) |- B(t, S z)   =>   Gamma |- D_(x,y) B(x,y)

where eta(z)=z exactly when the literal matrix is

  I(y,y;u.h) = I(y,y;v.k),

and eta(z)=0 otherwise. The counter and seed are the protected bound y.
This guard is preserved AND reflected by capture-free substitution.
Guarded zero instances compute to 0=0, so all ordinary case introductions
are recovered. Lifting an arbitrary equation into this diagonal shape then
recovers all native equation progress. Both translations preserve every
sequent literally. The existing whole-domain bi-interpretation with full
first-order iPRA therefore transfers.

PRECISE COMPARISON
Pinned repository: VladimirReshetnikov/ProveIt
Commit: 6bf83d8765614b0af51b35747e07fb057d6b2f42
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Matched, fully typed standalone checkers under CPython 3.12.14:
                         bytes    tokens   AST nodes   gzip-9
  native eight rules      3382      1101       1160        990
  witness seven rules     3205      1041       1099        975
  diagonal seven rules    3244      1069       1124        989

All figures concern complete modules after ast.unparse normalization.
Gzip is informational only. This reduces the eight-rule checker by 138
bytes, 32 tokens and 36 AST nodes. It is 39 bytes larger than the existing
witness-selected seven-rule variant. The benefit over that variant is
substitution invariance of its primitive introduction mode. The original
Q and D meanings and full formula grammar are retained.

This is NOT a new overall byte record: the 521-byte compact guarded-profile
checker remains smaller under its different input contract. No global
minimality or new Lean/Rocq verification is claimed. Written mathematical
proofs and checked finite certificates have different assurance levels.

RUN A CHECKER
From this directory (Python 3.10+ syntax; metrics pinned to Python 3.12.14):

  python3 code/diagonal_checker.py < tests/certificates/zero_computation.json

Acceptance is exit code zero and exactly ACCEPT plus a newline.
All other results reject. The checker validates terms, formulas, scopes,
contexts and every proof node. It imports only json and sys.

TRANSLATE A CERTIFICATE
The translator is untrusted and is not imported by any checker.
Its direction argument names the SOURCE calculus:

  python3 code/translate.py native < native.json > diagonal.json
  python3 code/diagonal_checker.py < diagonal.json

  python3 code/translate.py diagonal < diagonal.json > native_roundtrip.json
  python3 code/native_checker.py < native_roundtrip.json

The top-level format is exactly:
  {"variables": n, "context": [...], "goal": formula, "proof": proof_tree}

REPRODUCE
  python3 tests/reproduce.py
  python3 build.py

The first command regenerates measurements, checker regressions and both
proof-translation suites. The final command assembles the self-contained .tex and runs
pdflatex three times to settle the table of contents and references.
Standard TeX packages used are listed in the source.
The current evidence files record the actual completed run; consult them
for fixture counts and tested directions.
The translation suite can also be run alone with:
  python3 tests/test_translation.py

CONTENTS
  core_theorem.tex          New axiomatization and complete equivalence proof
  report_template.tex       Editable modular report source
  build.py                  Assemble and compile the standalone report
  code/                    Three standalone checkers and untrusted translator
  tests/                   Certificate producers and reproducible tests
  evidence/                Measurements, validation and provenance
  reference/inherited/     Exact inherited mathematical bridge sources
  reference/lean/          Selected upstream source for comparison only
  reference/ConciseIPRA_README.md  Exact pinned project overview
  LICENSE_ProveIt.txt       License for inherited repository material
  CLAIMS.json              Machine-readable claims and limitations
  MANIFEST.sha256           Integrity manifest for the packaged files

ATTRIBUTION AND FORMALIZATION STATUS
The diagonal dispatch and new single-rule comparison are the contribution
of this report. The scalar predecessor, equality reflection, pairing,
primitive-recursion compiler, ordinary logical macros and original native
bi-interpretation are inherited from ProveIt and are credited explicitly.
The selected Lean source snapshots are not a complete Lean checkout and
are not presented as a new mechanized proof. No remote repository was
modified in producing this package.
