A UNIFORM INTRODUCTION RULE FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Research prepared for Vladimir Reshetnikov, November 11, 2026

START HERE

Read ipra_uniform_progress.pdf. Its complete, self-contained LaTeX source is
ipra_uniform_progress.tex. The editable source is report.tex plus sections/.

RESULT AND LIMITATION

The new calculus R has seven primitive inference schemas. It keeps scalar
iterator terms and the unrestricted Eq/Q/D formula grammar. One introduction
schema selects its mode from the matrix root alone. At an equation matrix,
Q expresses progressivity; at a compound matrix, Q keeps the old conditional
closure reading. One reversed-iterator orbit elimination serves both cases.

The report gives explicit translations between R and the pinned native
calculus, derivation preservation, and both formula round trips over the
entire language. Composing with the inherited arithmetic bridge gives
bi-interpretability and equiconsistency with full first-order iPRA. Both
numerical domains are whole, equality is actual equality, and the numerical
composites are identities. No restriction to guarded public formulas is used
in R. These are written proofs, not newly Lean- or Rocq-checked metatheorems.

R is structurally simpler than the adopted eight-rule kernel. Its matched
straightforward checker is smaller than that kernel's checker, but larger
than the already existing seven-rule witness-sensitive kernel's checker.
Therefore this package does NOT establish a new globally smallest calculus
or a new minimum under every checker-size criterion.

MATCHED COMPLETE TYPED CHECKERS

                             Tokens    AST    Normalized bytes    Gzip 9
  Adopted native, matched      1235    1407          4692             1199
  New orbit R                  1206    1366          4553             1211
  Existing witness, matched    1173    1334          4456             1198

These standalone modules use the same explicit JSON syntax, scoping,
substitution, and public-grammar validation. The two old controls are newly
written implementations of the pinned rules, not Python files copied from
upstream. Measurements remove genuine docstrings, use ast.unparse plus one
newline, and count the entire standalone module. Gzip level 9 is informational.
The recorded environment is CPython 3.12.14 and zlib 1.3.2.

SEPARATE COMPACT IMPLEMENTATION IMPROVEMENTS

code/ancillary/ concerns the earlier GUARDED-SOURCE calculus, not R.
It improves the inspected coordinate minima from 257 tokens / 279 AST nodes /
522 bytes to 256 / 278 / 521. Different programs attain these minima.
The token-optimized program grows in bytes and gzip. Full measurements of
each program and its exact predecessor are in evidence/checker_metrics.json.

These compact programs retain the inherited canonical-public-goal contract;
they do not themselves validate the entire canonical public grammar. Their
numbers must not be compared directly with the typed checker numbers.
The gain composes existing implementation techniques and is not a new
axiomatization. See section 3 of the report for the exact scope.

REPRODUCING THE EXECUTABLE EVIDENCE

Run from this directory with Python 3.12 or a compatible later version:

  python3 code/orbit_checker.py < tests/certificates/identity_at_three_orbit.json
  python3 -B tests/reproduce.py

The first prints ACCEPT. The second regenerates the main certificates,
runs the process and rule controls, and rewrites metrics and verification
evidence using the current Python and compression versions. It uses only
the Python standard library. Detailed proof syntax is in code/README.txt.

The recorded run has 270 process expectations (122 acceptances and 148
rejections), two open-sequent controls, four capture-avoidance controls,
and zero mismatches. These finite controls do not prove the metatheorems.
The parity contradiction example has an explicitly false progressive
assumption; it is not a closed proof of contradiction.

BUILDING THE REPORT

  python3 build.py

This flattens the modular source and runs pdflatex three times. A normal
TeX installation with the packages named in report.tex is required.
Alternatively, compile ipra_uniform_progress.tex by itself twice with
pdflatex. The flattened file needs no other source files or external images.

PACKAGE GUIDE

  report.tex, sections/              Editable mathematical report
  ipra_uniform_progress.tex/.pdf     Standalone source and compiled report
  code/orbit_checker.py              Complete checker for the new R calculus
  code/native_checker.py             Matched native eight-rule control
  code/witness_checker.py            Matched existing seven-rule control
  code/ancillary/                    Separate compact guarded-source gains
  code/compressed/                   Normalized checker gzip streams
  tests/                            Certificates, producers, reproduction
  evidence/                         Measurements, results, inspection records
  reference/                        Authenticated inherited source material
  CLAIMS.json                       Machine-readable scope of the claims
  SHA256SUMS                        SHA-256 hashes of all other package files

REFERENCE SNAPSHOT

  Repository: VladimirReshetnikov/ProveIt
  Commit: a4e5e96c456303cf231eab2aeeb3291d8889833f
  Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

reference/PROVENANCE.json records immutable source paths, Git blob hashes,
and SHA-256 content hashes. Six incoming archives were also inspected and
authenticated; their blob identities are in evidence/incoming_archives.json.
The inherited source license is reference/LICENSE-ProveIt.txt (MIT-0).
The existing Lean sources were inspected, not rebuilt in this environment.
