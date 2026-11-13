LOCAL PROOF SCOPES AND INTERPRETATION OBSTRUCTIONS FOR iPRA
Prepared with ChatGPT, November 10, 2026

Read report.pdf (compiled from report.tex) for the complete argument.

STATUS
------
This is an honest research checkpoint. It does not claim the requested
significant new smallest axiomatization. The complete local-scope checker
is 668 normalized bytes, 284 tokens, and 323 AST nodes; its actual source
has a 391-byte gzip level-9 encoding. The inspected corpus's separate
minima are 672 bytes, 277 tokens, and 311 AST nodes. Only the byte coordinate
improves. The mathematical arithmetic/logical basis and its bi-interpretation
are inherited and explicitly attributed.

The main new mathematical result excludes EVERY ordinary finite-dimensional
first-order bi-interpretation of iPRA with the ordinary tied-seed B theory
(computation, coverage, separation, and literal-equation induction).
Arbitrary formula-defined domains, operation graphs, and quotient equality
are allowed. The proof combines finite profiles of B terms, finite witness
extraction from existential-free axioms, and the source-side return
isomorphism required for bi-interpretability. Provably inhabited finite
parameter families are also covered. It does not exclude equiconsistency
alone, all one-way interpretations, or theories with arbitrary additional
positive existence axioms. No literature-wide priority is claimed.

Supporting results include a finite-dimensional quotient obstruction for
term-defined units; exclusion of numerical equality, minimum, and truncated
subtraction as B terms; a zero-start recursor macro; and a direct numerical
completion using an unbounded selector. Adding bounded numerical primitives
preserves the weaker term obstruction, but need not preserve the finite
profiles used in the full bi-interpretation theorem.

The delivered 668-byte checker uses the inherited independent-initializer
I theory, which remains bi-interpretable with iPRA. It is distinct from the
obstructed B theory. The unbounded-selector completion is not claimed to
improve the size of a complete logical checker.

CONTENTS
--------
report.tex, report.pdf    Main paper, full rules, proofs, and limitations.
theory/                  Full obstruction proofs, selector repair, action lemma.
appendices/              Five unchanged, attributed iPRA bridge fragments.
code/checker.py           Entire 668-byte standalone proof checker.
code/checker.py.gz        Exact source compressed with gzip level 9, mtime=0.
code/readable_checker.py  Complete explanatory equivalent.
code/producer.py          Untrusted lexical serializer and example producer.
code/reference_*.py       Exact inherited producer and byte comparator.
code/verify.py            Finite positive/negative tests and guard controls.
code/verification.json    Complete execution receipt.
code/scope_argument.txt   Scope proof and exact compatibility limits.
audit/                   Independent whole-corpus inventory and normalizer.
audit/reference/         Six exact complete frontier sources and license.
evidence/                Metrics, hashes, reproduction and build receipts.
examples/                Ready-to-run positive and negative JSON inputs.
check_obstruction.py     Finite graph diagnostics for the combinatorial lemma.
reproduce.py             Reproduce all delivered checks and gzip measurements.
build.py                 Recompile report.pdf with latexmk.
package.py               Regenerate the manifest and deterministic ZIP.
MANIFEST.json            SHA-256 inventory of the packaged files.
CLAIMS.json              Machine-readable claim and limitation summary.

REPRODUCE
---------
Run from this extracted directory:

  python3 reproduce.py
  python3 code/checker.py < examples/I0_arbitrary_seed.json
  python3 code/checker.py < examples/contextual_induction.json
  python3 code/checker.py < examples/forged_witness_reject.json
  python3 build.py

The forged-witness example is supposed to print REJECT and exit nonzero.
All other displayed examples are supposed to print ACCEPT and exit zero.
The checker imports only Python's standard json library. It does not import
the producer, the measurement utilities, or a theorem library. Python's
ordinary recursion and memory limits can reject sufficiently large proofs;
mathematical completeness assumes unbounded resources.

The measurements were made with CPython 3.12.14 and zlib 1.3.2. Changing
Python or zlib can change normalized-source or gzip sizes. The exact source
and compressed byte strings are included. Gzip is informational only.

CORPUS PIN AND ATTRIBUTION
--------------------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     3fb35a5f2c0cb506180bede7ee3b9b5f93d4bc9d
Directory:  docs/drafts

All 16 direct ZIPs and nested provenance archives were inspected, giving
22 distinct archives and 297 distinct Python source byte strings. Their
hashes and the six complete Pareto-frontier sources are included. The large
proposal ZIPs themselves are not duplicated. To rerun the full scan:

  python3 audit/audit_corpus.py PATH_TO_PINNED_DRAFT_ZIPS AUDIT_OUTPUT

Use only the exact pinned inputs when reproducing the stated comparison.
The script requires semantic review if a newly nondominated source appears.

code/provenance.json and evidence/inherited_bridge.json record immediate
sources and hashes. The repository's MIT No Attribution license is included.
The inherited bridge is not relabeled as a new result. Neither finite tests
nor the independent written reviews are proof-assistant formalizations.
