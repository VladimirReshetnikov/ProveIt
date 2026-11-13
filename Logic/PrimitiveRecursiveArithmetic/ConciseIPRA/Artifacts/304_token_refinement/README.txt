CONCISE iPRA: A 304-TOKEN FULLY VALIDATED CHECKER
Research report, 13 November 2026

RESULT AND LIMITATION
The new complete checker code/checker304.py measures:
    304 significant tokens / 361 AST nodes / 705 normalized UTF-8 bytes.
Its exact matched control measures 306 / 362 / 668.
The change replaces continuation recursion by a loop. Recursive checking
of a major premise remains. The accepted certificates are unchanged under
the repository's ideal finite-execution convention.

This improves the token minimum of the fully validated native Eq/D family
at the inspected snapshot. It is an implementation refinement of the
existing iPRA presentation, not a new mathematical axiom basis. It does not
beat the compact envelope 239 / 255 / 461, nor the strict AST minimum 348
or strict byte minimum 589. No absolute simplicity lower bound is proved.
The stronger requested construction below the entire frontier remains open.

START HERE
report.pdf                       Complete report and proofs.
report.tex                       Editable LaTeX source.
code/checker304.py                Complete new standalone checker.
benchmarks/strict_tokens306.py    Exact unchanged matched control.
fixtures/three_field_cases.json   65 inherited test cases with provenance.
evidence/verification.json        260 normal/-O subprocess executions.
evidence/loop_trace_review.json   Independent 9,461-node trace comparison.
evidence/measurements.json        Remeasured complete modules and hashes.
reference/                       Attributed inherited foundations.

RUN AN ACCEPTED EXAMPLE
    python3 code/checker304.py < examples/zero_computation.json
    python3 code/checker304.py < examples/equation_induction.json
Normal success prints exactly ACCEPT and a newline. An exception rejects.
The supplied examples/rejected_scope.json must reject.

REPRODUCE
Use CPython 3.12.14 for the exact published source-size coordinates.
    python3 verify.py
    python3 tools/review_loop.py
    python3 tools/verify_manifest.py

The verifier and trace reviewer are untrusted development tools, not
imports of the measured checker. The checker imports only Python's JSON
parser. Finite tests supplement the written simulation proof.

BUILD THE REPORT
    sh build.sh
Requires pdfLaTeX with standard AMS, geometry, booktabs, listings,
hyperref, xurl, microtype and Latin Modern packages. No network is needed.
Building or re-running verification may change generated evidence/PDF
metadata, so verify the original manifest before rebuilding the package.

INPUT CONTRACT
The checker reads one complete JSON array. The final item is the closed
native Eq/D goal; earlier items are proof packets consumed from the end.
All parsed input values, including unused prefixes, are checked to be exact
integers or lists. The public-goal arities, parity and scope are checked.
Unused valid integer/list prefixes are permitted, as in the control.
There is no new certificate translator. No assert is used by the checker.
Physical recursion/memory limits are outside mathematical completeness.

PROVENANCE AND STATUS
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 7a7633980dbca7f599322a5e7f1e65fb1cddb7c8
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The four current incoming archives were included in the benchmark audit.
The theory's full iPRA bi-interpretation is inherited, with whole numerical
domains, actual equality, formula round trips and identity numerical maps.
The new program equivalence is a written proof with independent review;
it is not a new Lean/Rocq formalization of Python or of the arithmetic bridge.
Inherited sources retain their MIT No Attribution license.
