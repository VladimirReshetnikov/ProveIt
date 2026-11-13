Smaller presentations of iPRA
============================
Two checker records and a fused finite-block translation
Prepared for Vladimir Reshetnikov, 12 November 2026.

READ FIRST
report.pdf is the 18-page mathematical and implementation report.
report.tex and mathematics/fused_blocks.tex are its complete LaTeX sources.

RESULT
The pinned current compact-checker envelope is 240 significant Python
tokens / 259 AST nodes / 462 normalized bytes, attained by different files.

New complete programs:
  checkers/code/checker_tokens239.py : 239 tokens / 261 nodes / 549 bytes
  checkers/code/checker_ast256.py    : 245 tokens / 256 nodes / 580 bytes

Both preserve the inherited checking relation and hence its full iPRA
bi-interpretation. They change no primitive arithmetic or logical axiom.
The new observed envelope is 239 / 256 / 462; no one new file attains it.

The mathematical result is a finite-conjunction/disjunction compiler in
the native Eq/D language. Its fully expanded branch cost is 62 term nodes,
against the documented 66 and an immediate floor-ramp improvement to 64.
It uses one additional paired binder for the entire finite block. The exact
size theorem and the restricted optimal-padding theorem are proved in full.

WHAT REMAINS OPEN
A new primitive axiom basis below the entire checker envelope, one checker
beating all prior coordinate minima simultaneously, and absolute minimality
have not been established. This archive makes no such claims.

INPUT CONTRACT
The compact checkers read JSON Lines: a canonical closed guarded Eq/D
goal first, then three-field proof packets. Inputs are finite exact-integer
and list trees. The public grammar and the full JSON alphabet are promised,
not independently validated. Acceptance is normal termination with exactly
ACCEPT followed by a line feed; an exception rejects. Finite ideal runs
define the theorem relation, without fixed physical resource limits.

EXAMPLE
  python3 checkers/code/checker_tokens239.py < \
    checkers/fixtures/global_computation_zero.jsonl

REPRODUCE
Use Python 3.12.14 for exact source metrics.
  python3 verify_manifest.py
  python3 checkers/verify.py
  python3 mathematics/fused_finite_blocks.py
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Check the original manifest before rebuilding files, since PDF metadata may
change. Test evidence is finite; the universal proofs are in the report.
No repository import is needed for the checks above. Recompute the complete
repository census, if the pinned repository is available, with:
  python3 checkers/census.py /path/to/ConciseIPRA new_census.json

CONTENTS
checkers/code/         Two record sources and readable standalone form.
checkers/controls/     Matched and record controls, attributed in evidence.
checkers/fixtures/     Thirty accepted/rejected proof inputs.
checkers/evidence/     Static census, source hashes and verification receipts.
mathematics/          Fully expanded formula compiler, proof source and checks.
reference/            Frozen source chapters and independent written reviews.
CLAIMS.json           Explicit claims, nonclaims and contracts.
MANIFEST.sha256       Integrity hashes for the delivered files.

PROVENANCE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: 1156099ffe30f7497d2c11ab20271f46cffcd115
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The native calculus, its ordinary bridge, arithmetic floor/absorbing terms,
input codec, matched controls and inherited fixtures are credited to the
repository. The original MIT-0 license is included.

The new parts are the verified implementation refinements and the use of
the absorbing transition to fuse finite-block selection and continuation.
No new Lean or Rocq formalization is claimed.
