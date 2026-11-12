iPRA: A FRONTIER AUDIT AND VERIFIED CHECKER REFINEMENTS
Prepared for Vladimir Reshetnikov, November 12, 2026
====================================================

RESULT STATUS
-------------
The requested axiomatization below the current global complexity frontier
was NOT obtained. This package states that limit explicitly.

Verified partial results:

  native public-goal checker: 629 -> 623 -> 622 normalized source bytes
  whole-input/native checker: 646 -> 645 normalized source bytes

Tokens and AST nodes increase. No mathematical axiom or rule is deleted.
The current compact envelope remains 248 tokens / 270 AST nodes / 487 bytes,
attained by different programs and under a guarded public-input contract.

There is also a proved scoped-export lemma: a delayed retained conclusion
after a global minor proof can be supplied through its existential closure.
This is a separate mathematical observation, not a completed proof of an
entire new global checker. The recommended checkers do not depend on it.

START HERE
----------
ipra_checked_frontier.pdf      Complete report with attributed foundations.
ipra_checked_frontier.tex      Flattened standalone LaTeX source.
sections/                     Editable authoring source.
checkers/native_append_function.py
                              Clearest new implementation, 623 bytes.
checkers/native_append_lambda.py
                              Equivalent 622-byte expression form.
checkers/strict645_lambda.py   Whole-input alphabet + native goal validation.
checkers/native_control.py    Exact 629-byte matched control.
checkers/strict646_control.py  Exact 646-byte matched control.
baselines/                    Exact current compact records and strict654.
reference/                    Attributed inherited mathematical proofs.
evidence/                     Source audit and independent review.
CLAIMS.json                   Machine-readable result boundaries.
MANIFEST.sha256               SHA-256 integrity ledger.

COMPLETE-MODULE METRICS (CPython 3.12.14)
---------------------------------------
Program                         Tokens   AST   Normalized bytes
native_control.py                  324    374     629
native_append_function.py          330    379     623
native_append_lambda.py            335    383     622
strict646_control.py               343    392     646
strict645_lambda.py                348    396     645

Normalization: ast.unparse(ast.parse(source)) plus one LF. Significant
tokens exclude whitespace/newline/indent/comment/encoding markers. Every
AST node and normalized UTF-8 byte of each complete module is counted.
The standard JSON reader is the only imported library in the checkers.

INPUT CONTRACTS
---------------
The new programs consume ordinary multiline JSON arrays from their right
end. The last item is the public goal. Remaining packets have four fields.
Normal exit with exactly ACCEPT plus LF is acceptance; exceptions reject.
Unused prefixes are allowed.

native_append_* validate the closed full native Eq/D public goal. Their
theorem contract assumes finite integer/list certificate trees; they do
not independently enforce that alphabet throughout every unused prefix.
strict645_lambda.py checks both the whole-input alphabet and native goal.
Do not identify either interface with the compact guarded baseline grammar.

The 248-token and 270-AST baseline programs use one physical line of JSON;
later lines are outside their frame. The 487-byte baseline uses multiline
JSON. Those three baseline metrics do not describe one executable.

REPRODUCE
---------
From this extracted directory:

  python3 reproduce.py

This verifies the manifest, measures the supplied baselines and new modules,
checks the exact source/AST transformations, repeats 440 isolated standalone
normal/-O fixture executions, and repeats the independent 15-run event-trace
comparison. Results are written to the included JSON receipt locations.
Finite tests supplement the report's universal simulation proof.

Example of the strict entry point:

  python3 checkers/strict645_lambda.py < checkers/fixtures/strict/proofs/computation_zero_local.json

To rebuild the standalone TeX and PDF:

  python3 build_report.py --pdf

Or compile the flattened source directly with pdflatex twice. It contains
all source listings and appendices and needs no external input files.
No network access is required for reproduction or the PDF build.

MATHEMATICAL CONTENT
--------------------
The report explicitly gives the inherited scalar syntax, both computation
schemas, all native logical/equality inference rules, and freshness and
induction restrictions. Its ordinary realization is bi-interpretable and
equiconsistent with full first-order iPRA on whole numerical domains with
actual equality and identity numerical composites x=y. These foundations
are inherited, attributed and reproduced; they are not new results here.

New implementation contribution: exact mutable-state truthy-return
composition with the current native profile and outer-lambda composition
with the strict profile. Both techniques themselves occur upstream.

Separate new lemma: delayed equality targets need existential supply,
not a claim that they hold for arbitrary fresh names. The report proves
the decoded-formula substitution identity and both retained equality and
retained closure export rules. Full raw-checker completeness is not claimed.

No absolute minimum, no improvement below all compact records, no new
Lean/Rocq formalization, and no repository mutation is asserted.

PROVENANCE
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: ecae4653f69184a25ade2b1aeaa346f7a7817b78
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All nine current incoming archives were authenticated by Git blob hash.
evidence/source_audit.json retains the original audit receipt; its historical
local paths refer to the audit environment, while the repository paths and
hashes identify the source unambiguously. The supplied selected baselines
are remeasured without fetching the full source corpus.

Inherited software and written proofs retain the included MIT-0 license.
The new code and prose may also be used under that license.
