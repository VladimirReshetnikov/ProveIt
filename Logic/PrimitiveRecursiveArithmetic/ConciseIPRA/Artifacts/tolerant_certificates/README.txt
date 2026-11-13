A SMALLER TOTAL PROOF CHECKER FOR iPRA
12 November 2026

RESULT AND LIMIT
The selected standalone checker is 315 significant Python tokens, 361 AST
nodes, and 603 normalized UTF-8 bytes under CPython 3.12.14. It is sound for
arbitrary parsed proof data, and validates its public goal. Its mathematical
execution terminates on every finite parsed input.

This DOES NOT meet the full request to beat the smallest current proposals.
The incoming-inclusive compact envelope is 244 / 265 / 477, attained by
different programs. No new logical/arithmetic axiom deletion or absolute
minimality theorem is claimed.

The candidate is numerically below each coordinate of the exact-alphabet
envelope 330 / 380 / 621. It deliberately accepts harmless numeric spellings
and irrelevant unused data, so this is NOT an identical-contract comparison.
The decoded native theorem set and its inherited full iPRA bi-interpretation
are preserved. Completeness is established for canonical encodings and their
numeric respellings, not separately for every dummy-slot representation that
the sorted public grammar admits.

MAIN FILES
ipra_tolerant_certificates.pdf  Compiled paper.
ipra_tolerant_certificates.tex Editable LaTeX source.
sections/                     New proof and verification summary.
code/checker.py                Complete measured acceptance program.
validation/                   Self-contained executable verification bundle.
evidence/                     Audits, source hashes, and internal reviews.
reference/                    Pinned inherited mathematics and baseline code.
CLAIMS.json                   Explicit positive claims and unmet targets.
MANIFEST.sha256               File hashes (except the manifest itself).

RUN THE CHECKER
From this directory, with Python 3.12:

  python3 code/checker.py < certificate.json

A certificate is one JSON array: the last element is the public goal and
the earlier elements form a reverse-consumed four-field proof-packet stack.
Normal exit with the line ACCEPT is acceptance. All exceptions and parser
failures are rejection. An unused prefix is allowed. There is no proof search.
The parser is Python's standard json module; its accepted NaN and Infinity
extensions are included in the arbitrary-data soundness analysis.

REPRODUCE THE VERIFICATION
See validation/README.txt for exact switches. The main command is:

  python3 validation/test_harness.py

The delivered receipt records 388 actual CLI runs, including -O, with zero
failed expectations; 44,416 bounded false-goal trials all reject. No false
goal trial reached a recursion or call-budget limit. These finite checks are
supporting evidence, not substitutes for the mathematical proof.

REBUILD THE PAPER
With a standard LaTeX installation including the listed packages:

  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_tolerant_certificates.tex

PROVENANCE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Revision: eb0e0e00147e9f8d29737ff58587852008ecf4c3
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All seven incoming ZIPs at that revision were authenticated by Git blob hash.
The selected program starts from incoming ipra_refinement_2026-11-12(1),
checkers/code/native_tokens.py. It deletes the exact-integer object guard
and replaces the array test a*0 != 0 by a*0 == []. The inherited exact-alphabet
gate is absent; its necessity is the point addressed by the new proof.

The inherited source chapters are preserved for the bridge and protocol
lemmas. They are not runtime dependencies. Inherited code/documentation is
under the supplied MIT No Attribution license. No Lean or Rocq proof for the
new result is claimed, and the inherited Lean build was not rerun.
