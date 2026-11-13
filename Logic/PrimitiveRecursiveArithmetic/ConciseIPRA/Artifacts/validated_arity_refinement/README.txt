THREE SMALLER VALIDATED PRESENTATIONS OF iPRA
November 13, 2026

RESULT AND LIMIT

The complete whole-input-validated checker family improves its measured
coordinate envelope from 319 tokens / 358 AST nodes / 599 normalized bytes
to 317 / 356 / 597. Different complete programs attain the coordinates.
Exact equivalence with each control preserves the full iPRA theory.

This is an implementation refinement. No arithmetic axiom or inference
rule is deleted. The separate compact, promised-input envelope
239 / 256 / 461 is NOT beaten. A new mathematical axiomatization below
all current proposals remains unestablished. Gzip sizes increase.

START HERE

report.pdf                 compiled paper
report.tex                 complete editable LaTeX source
metrics_table.tex          exact measurements used by the paper
verification_summary.tex   verification counts used by the paper

The paper gives all eight native schemas, logical macros, the ordinary
arithmetic realization, inherited interpretation maps and both round trips,
and universal proofs of the two program transformations.

COMPLETE CHECKERS

Profile  File                            Tokens  AST  Bytes  gzip-9
Token    code/checker_strict_tokens317.py   317    368   634    398
AST      code/checker_strict_ast356.py      325    356   646    399
Byte     code/checker_strict597.py          328    372   597    392

Each accepts a whole JSON document, validates its exact integer/list
alphabet and closed native Eq/D public goal, and checks the proof.
Internal proof records retain the established sorted-arity semantics.
An unused packet prefix is allowed. The byte profile has a different
packet ordering from the other two, exactly as its control does.

The measured modules import only the standard-library JSON reader.
The .py.gz files use gzip level 9 and mtime=0 on normalized source;
they are distribution copies, not executable source loaders.

REPRODUCE

From this directory, using Python 3.12.14 for exact size reproduction:

    python3 verify.py

This checks all three candidate/control pairs and the stated rewrites.
There are 468 ordinary/optimized subprocess executions: 296 across
37 context-update fixtures and 172 across 43 byte-profile fixtures.
The receipts record zero failures, plus 4,810 arity identity comparisons.
Finite tests support implementation validation; universal equivalence is
proved in the paper. No new end-to-end Lean/Rocq verification is claimed.

Examples:

    python3 code/checker_strict_tokens317.py < examples/token_zero.json
    python3 code/checker_strict_ast356.py < examples/token_zero.json
    python3 code/checker_strict597.py < examples/byte_zero.json

Acceptance prints ACCEPT and exits successfully. Invalid input may raise
an exception. Mathematical completeness uses ideal unbounded finite
execution; physical parser, memory and recursion limits can reject large
valid certificates.

BUILD THE PAPER

    python3 build_pdf.py

The helper uses installed TeX only. If the format cache is unavailable,
it creates a private format from installed sources; it downloads nothing.
A conventional installation can instead run pdflatex twice on report.tex.

PROVENANCE

Repository: VladimirReshetnikov/ProveIt
Commit:     95d3dd192e97a19bd4f8783c764331ec41126264
Directory:  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The census covers 3,578 tracked Python/gzip entries under Artifacts and
Python/gzip members of all five current incoming ZIPs. Nested historical
ZIPs are not recursively expanded. There are 1,964 distinct source byte
strings. Selected program contracts were inspected; static measurement
does not certify every script. No absolute lower bound is claimed.

Optional census against a local checkout:

    python3 census.py /absolute/path/to/ProveIt /absolute/path/to/census-output

Use the pinned commit for matching results. The script records the
checkout identity and does not execute corpus sources.

CONTENTS

controls/                  exact matched controls
fixtures/                  compact inherited regression cases
reference/frontier_controls/ selected baseline comparison sources
reference/PROOF.txt         universal arity-erasure proof
reference/FAMILY_PROOF.txt  context-extension proof and attribution
evidence/metrics.json       exact new/control measurements
evidence/reviewed_frontier.json  contracts and observed extrema
evidence/source_census.json     complete static source inventory
evidence/source_census.csv      tabular inventory
CLAIMS.json                precise claim boundaries
PROVENANCE.json            source and transformation attribution
MANIFEST.sha256            checksums of packaged deliverables

The byte-extension identity was already published in procedure_presentation;
this delivery composes it with the later checked_presentations profiles.
The arity-erasure predicate is the separate new rewrite.
The mathematical iPRA basis and bridge are inherited and attributed.
LICENSE-ProveIt.txt supplies the repository's MIT-0 terms.

