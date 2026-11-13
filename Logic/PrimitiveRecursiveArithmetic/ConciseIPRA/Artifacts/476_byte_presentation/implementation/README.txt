IMPLEMENTATION APPENDIX: TWO EXACT PYTHON REFACTORINGS
===================================================

These files are supplementary to the mathematical report. They are NOT a
new axiomatization, a cognitive-simplicity result, or a claimed solution to
the compact-checker minimization target.

Recommended arbitrary-JSON interface:

    python3 strict_bytes.py < fixtures/strict_proofs/computation_zero_local.json

Accepting certificates produce exactly ACCEPT followed by a newline and
terminate with exit status zero. Every other outcome rejects. No validation
depends on assert or changes when Python is run with -O.

Whole-module metrics (CPython 3.12.14, ast.unparse plus LF):

                          tokens  AST nodes  bytes
native_tokens.py             319       369    622
native_ast.py                321       367    626
native_bytes.py              332       379    594
strict_size.py               328       378    642
strict_bytes.py              338       384    619

The native profiles validate the native Eq/D public goal, while retaining
the inherited exact-integer/list promise for consumed certificate fields.
The strict profiles also validate the entire input alphabet, including
unused prefixes. The current compact-record profiles use a weaker contract
that assumes a canonical guarded public goal. Do not compare these interfaces
as if they were the same.

PROOF.txt gives two elementary universal program arguments: byte iteration
extends an ordinary list by the same integer zero; and the validation flag
can default to the public phase when internal calls pass zero explicitly.
Every program remains standalone and imports no file from this directory.

Reproduce all exact source checks, metrics and 880 inherited certificate
executions (controls and candidates, normal and -O):

    python3 verify.py

The delivered verification.json has zero failed expectations. The fixtures
and controls are frozen unchanged from their cited current incoming archive.
PROVENANCE.json identifies its pinned repository path, Git blob identity,
SHA-256, member paths, and individual file hashes. The inherited MIT-0
license is retained. Finite tests supplement the program proofs; neither is
a new proof-assistant formalization of the complete iPRA bridge.

CENSUS_NOTE.txt and frontier_census.json document the current repository and
incoming comparison. The broad compact envelope is (244,265,477), attained
by different programs and NOT improved here. The stronger native validation
envelope becomes (319,367,594), and the strict envelope (328,378,619), again
by different programs. These are exhibited implementation sizes, not proved
lower bounds.

For a fresh static census at the pinned checkout:

    python3 audit_frontier.py /path/to/ProveIt

No candidate source is executed by the census.
