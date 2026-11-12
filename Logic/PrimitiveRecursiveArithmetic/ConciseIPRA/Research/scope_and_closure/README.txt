iPRA: scope-preserving checker composition and mixed closure
===========================================================

STATUS
The requested simpler mathematical axiomatization has NOT been established.
This package provides two narrowly smaller implementations of the existing
calculus, a different mathematically proved presentation, and a precise
obstruction to one proposed arithmetic simplification. It makes no global
minimality claim and no new Lean/Rocq verification claim.

Comparison snapshot
VladimirReshetnikov/ProveIt at
8662bc0a00f4e77e482f7d141d7a4f919f70f9aa
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Measured complete modules (tokens / AST nodes / normalized UTF-8 bytes /
gzip level 9 bytes, CPython 3.12.14):
  reference/checker_ast.py:   263 / 289 / 613 / 349
  code/checker_ast.py:        264 / 288 / 608 / 350
  reference/checker_bytes.py: 266 / 310 / 529 / 333
  code/checker_bytes.py:      267 / 309 / 528 / 336

The AST and byte improvements are in DIFFERENT programs. The inspected
261-token coordinate is not beaten. Gzip sizes increase and are FYI only.
The underlying calculus, arithmetic, and interpretation do not change.
The underlying prevalidation idea already exists in the repository; see
CHANGE.txt for attribution and an accepted-certificate equivalence proof.

FILES
  report.pdf / report.tex     Complete paper and standalone TeX source.
  code/                      Two complete checkers and their gzip-9 copies.
  reference/                 Frozen comparison checkers, inherited written
                             proofs, current README, and upstream license.
  theory/mixed_closure.tex    Different deterministic introduction scheme;
                             both interpretations and both composites proved.
  theory/zero_start_obstruction.tex
                             Monotonicity and exact scalar zero-set theorem.
  tests/cases.json            49 frozen arithmetic/logical/control certificates.
  tests/results.json          504 CLI checks plus 6 mutation-control runs.
  evidence/metrics.json       Whole-module metrics.
  evidence/novelty_screen.json
                             Exact AST screen; NOT conceptual novelty evidence.
  evidence/source_manifest.json
                             Pinned source paths and hashes.
  CLAIMS.json                Machine-readable scope and limitations.
  MANIFEST.sha256             Integrity ledger of the delivered package.

REPRODUCE
  python3 measure.py
  python3 verify.py
  python3 code/checker_bytes.py < tests/example_accept.json
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Success means exit status zero AND exact stdout 'ACCEPT\n'. Parsing/checking
exceptions reject. The checkers read JSON data and do not evaluate Python
supplied in a certificate. No checker imports the test, measurement, build,
or provenance utilities. Reproduction of Python evidence needs only Python's
standard library. Reproduction of the PDF needs a normal TeX installation
with the packages named in report.tex. No repository/network fetch is needed.

The report.tex file already embeds all sections and its code listing. To
edit the separate section sources and reassemble that standalone file, run
python3 build_report.py before the two pdflatex commands.

MIXED-CLOSURE RESULT
The new alternative reads Q(E) for a literal equation as progress, but Q(B)
for a compound matrix as the existing base-to-all closure. Padding every old
binder matrix gives an effective embedding of the old core; full formula
round trips and identity numerical composites are proved. Its introduction
has no independent mode. Elimination now uses an iterator term and an extra
numerical parameter, so this presentation is NOT claimed smaller overall.
Closure is syntax-sensitive. Congruence is proved only within the same
matrix category, never across atomic/compound matrices.

VALIDATION LIMIT
The numerical tests validate implementations; they do not formalize the
mathematical metatheorems. Written arguments have been checked for circular
bootstrap, witness freshness, induction strength, and both composites.
The copied arithmetic bridge and its original attribution remain explicit.

The zero-start obstruction is for same-domain standard term definitions.
It does not rule out the changed domains or graph interpretations permitted
by the research question. Further research questions appear in the paper.
