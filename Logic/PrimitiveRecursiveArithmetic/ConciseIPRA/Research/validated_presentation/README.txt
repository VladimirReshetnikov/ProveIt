A SMALLER VALIDATED CHECKER FOR THE CONCISE iPRA AXIOMATIZATION
Prepared for Vladimir Reshetnikov, 11 November 2026.

RESULT AND LIMIT

The selected complete Eq/Q/D checker is 870 normalized Python bytes,
383 significant tokens, and 442 AST nodes. Its matched incoming control is
897 bytes, 401 tokens, and 468 AST nodes. Gzip-9 grows from 505 to 507 bytes.

The Eq/D public-language variant is 849 bytes / 370 tokens / 426 AST nodes,
against 878 / 390 / 454. Gzip-9 grows from 498 to 499 bytes.

This is a proved implementation simplification of the existing complete
presentation, not a new mathematical axiomatization or a breakthrough in
the arithmetic basis. The proof kernel is unchanged. No new reduction
below the existing seven-rule mathematical presentations was established.
No absolute minimality is claimed. The 521-byte guarded checker has a
different input contract and is not beaten by this result.

MAIN FILES

ipra_validated_presentation.pdf   Complete compiled report.
ipra_validated_presentation.tex   Expanded standalone LaTeX, including code.
report.tex and theory.tex        Editable report component sources.
code/native_typed_full.py        Selected complete full Eq/Q/D checker.
code/native_typed_eqd.py         Selected Eq/D public-language variant.
code/annotated_checker.py        Same full checker with explanatory comments.
code/native_lexical.py           Correct but larger lexical alternative.
reference/                      Exact matched controls and attributed proofs.
tests/                          Inherited certificates and malformed inputs.
evidence/metrics.json            Reproducible whole-program sizes.
evidence/validation.json         Detailed validation receipt.
evidence/independent_review.txt  Independent assistant implementation review.
reference/provenance.json        Repository pin, Git blob identities, hashes.
CLAIMS.json                     Exact claims and limitations.
SHA256SUMS                      Final package file hashes.

RUN

From this directory:
    python3 code/native_typed_full.py < tests/native_computation.json
    python3 -O code/native_typed_full.py < tests/native_computation.json

Both print ACCEPT followed by a newline and exit normally. An exception
or any other outcome is rejection. A selected checker imports only json
from the Python standard library. No auxiliary files are needed to check
a certificate.

REPRODUCE

    python3 reproduce.py
    python3 build_report.py

The first command runs offline with the Python standard library; use
CPython 3.12.14 to reproduce the stated ast.unparse coordinates exactly.
The second generates the standalone TeX and its PDF using pdflatex and
standard LaTeX packages. It also regenerates the report tables and gzip
artifacts. A working TeX installation with initialized formats and font
maps is needed. The expanded TeX can also be compiled directly.

WHAT CHANGED

For values returned by the unchanged JSON parser, this expression is true
exactly for trees of exact integers and lists:

    not repr(q).strip('0123456789[], -')

Every other JSON result type contributes a forbidden representation
character. This checks the whole certificate, including unused prefix
elements. The public syntax validator can then lose its separate raw-type
mode and work at the original binding depth. The old and new scoped
validators satisfy V_new(a,d) iff V_old(a,d+2). The function c has the same
AST as its matched control.

The complete explicit axiomatization, both iPRA interpretations, both
formula and numerical round trips, and the inherited internal arithmetic
proofs are included in the report. Both interpretation domains remain
whole, equality remains actual equality, and the numerical isomorphisms
are defined by x=y.

VALIDATION

For each public-language profile:
  21,024 JSON-derived values against independent exact type recognition;
  240,120 old/new scoped-validator comparisons;
  101 existing input fixtures, all matching the control;
  11 malicious unused-prefix types in normal and optimized Python;
  JSON whitespace, integer digit limits, and unchanged kernel AST checks.

Full profile: 21 accepted fixtures, 80 rejected.
Eq/D profile: 16 accepted fixtures, 85 rejected.
One of the 101 input fixtures is a metadata-shaped object deliberately
rejected as malformed certificate input. Zero mismatches were found.

These finite checks support the written proofs. The Python implementation
has not been verified in Lean or Rocq. Existing Lean sources were inspected,
not rebuilt. The appendices and exact kernel control are inherited from
ProveIt, not newly proved by testing.

RESOURCE AND ERROR QUALIFICATIONS

The intended data language and mathematical certificate contract are
preserved. Resource-limit behavior can differ: an unused integer/list prefix
nested 600 levels exhausts the old raw validator in the tested environment
but is accepted by the new one when appended to a valid proof. Identical
subprocess outcomes at every finite hardware limit are not claimed.

The diagnostic sentence is retained, but rejected null/dictionary values
can produce ValueError instead of the old TypeError. Both reject.

BASELINE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 42a48d2f04ad72036e8d7e365ea91ea08c76a9e3
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Matching incoming archive: docs/incoming/ipra_validated_core_2026-11-11.zip
The incoming one-sided-transport archive was also inspected.

ATTRIBUTION

The arithmetic, native logic, certificate kernel, proof fixtures, and
inherited mathematical appendices come from the pinned ProveIt development
under its MIT No Attribution license. A copy of that license is included.
The present contribution is the smaller validation boundary and its proof.
The reviews are assistant reviews, not external human reviews.
