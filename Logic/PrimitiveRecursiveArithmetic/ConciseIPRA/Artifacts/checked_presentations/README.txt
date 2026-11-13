SMALLER CHECKED PRESENTATIONS OF iPRA
Research report, 13 November 2026
================================================

OPEN FIRST

  ipra_checked_presentations.pdf
  report.tex

RESULT AND LIMIT

This package provides verified reductions in complete implementations of
existing iPRA presentations. It does not provide a newly simplified
mathematical axiom basis or a proof of global minimality. The stronger
research request remains open.

Complete normalized-source measurements (CPython 3.12.14):

  code/strict_tokens.py     319 tokens   370 AST nodes   630 bytes
  code/strict_ast.py        327 tokens   358 AST nodes   642 bytes
  code/strict_bytes.py      335 tokens   380 AST nodes   605 bytes
  code/compact_stream.py    240 tokens   266 AST nodes   592 bytes
  code/compact_whole.py     245 tokens   272 AST nodes   591 bytes

The strict programs validate the whole parsed JSON alphabet and the full
native Eq/D public grammar. Numerical zero is the scalar code 1; numerical
one is [1]. Administrative instruction markers are separate. Their prior
zero-as-one controls give a coordinatewise envelope 331 / 373 / 608; the
new programs give 319 / 358 / 605. Different programs attain the minima.

The compact programs assume exact-integer/list trees and a canonical closed
guarded public goal. The stream program improves its incoming matched
control from 242 to 240 tokens. The whole-JSON matched comparison is
247 -> 245 tokens. Those programs do not improve the independent compact
262-AST and 469-byte records. Do not combine coordinates into a fictitious
single program, or compare validation contracts without stating them.

MATHEMATICAL STATUS

The report states every primitive rule and distinguishes the full native
reading from the guarded compact auxiliary reading. Written equivalence
proofs preserve the existing theorem sets. The established iPRA bridge is
reused with whole domains, actual equality, both formula round trips, and
identity numerical comparison graphs x=y. There is no new Lean/Rocq
verification of the Python programs.

Independent review found and repaired a real induction-mode bug in an
earlier candidate. The delivered terminal selector permits progress only
when len(matrix) == marker == 2. The rejected version is not delivered as
a usable checker.

CONTENTS

  report.tex, ipra_checked_presentations.pdf
      Complete report, proofs, comparison, limits, and further questions.
  code/
      Five standalone measured programs. Each imports only Python's
      standard library and prints ACCEPT on successful normal exit.
  strict/
      Exact strict controls, 141 fixture files, untrusted certificate
      translator, proof notes, provenance, and reproducible verification.
  compact/
      Stream and whole-JSON controls, fixtures, exact correspondence proof,
      provenance, and reproducible verification.
  reference/
      Pinned upstream base/guard/checker chapter fragments and the Lean
      bi-interpretation theorem source, with the upstream MIT-0 license.
  review/
      Independent mathematical/scope audit and compact correspondence proof.
  evidence/
      Combined metrics, source checksums, and reproduction summary.
  reproduce.py, CLAIMS.json, PROVENANCE.json, MANIFEST.sha256
      Reproduction driver and precise boundaries of the claims.

REPRODUCE

  python3 reproduce.py --verify-manifest
  python3 reproduce.py --metrics-only
  python3 reproduce.py
  python3 reproduce.py --pdf

The default command recomputes metrics and runs both packaged suites.
--pdf additionally builds the report; it requires the installed LaTeX
packages declared in report.tex. No Python verification step needs network
access or a nonstandard Python package. Reproduction writes fresh evidence,
so verify the manifest before regenerating files, or work in a copy.

Examples using the standalone modules:

  python3 code/compact_stream.py < compact/fixtures/lines/global_shared_computation.jsonl
  python3 code/compact_whole.py < compact/fixtures/whole/global_shared_computation.json

For strict examples, use the matching code/ profile and entries listed in
strict/fixtures/cases.json. The supply and terminal certificate protocols
are different; a certificate for one is not necessarily accepted by another.

VERIFICATION

The packaged results contain 808 strict process executions, normally and
under -O, 19 reproduced terminal translations, 160 compact process
executions, and 416 seeded compact trace comparisons, all with expected
results. These finite checks support the written proofs; they do not prove
universal soundness or bi-interpretability. The induction-mode boundary
regression extracts the selector from the actual delivered checker source.

PINNED REPOSITORY

  https://github.com/VladimirReshetnikov/ProveIt
  31e1e9220868788a85ca5fea351d7ab4097cfa4a
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All twelve incoming ZIP archives at that pin were inspected, and their
byte lengths and Git blob identities verified. No repository write,
commit, pull request, or publication was made.
