A SMALLER VALIDATED PRESENTATION OF iPRA
13 November 2026
======================================

Read report.pdf (editable source: report.tex).

RESULT AND UNMET TARGET
----------------------
Three new complete standalone checkers improve the observed validated
coordinate envelope from 302 tokens /340 AST nodes /584 normalized bytes
to 300 /337 /580. Different programs attain the coordinates.

This does NOT beat the compact promised-grammar envelope 239 /255 /460.
No globally simplest axiomatization, absolute complexity lower bound,
new deletion of arithmetic/logical axioms, or mathematical breakthrough
is claimed. The original stronger minimization target remains open.

The public theory is the existing full first-order native iPRA presentation,
with its inherited bi-interpretation: whole numerical domains, actual
equality, both formula round trips, and identity numerical graph x=y.
The changes are proved checker refinements and a composition of existing
certificate mechanisms. They retain the exact equation-only progress test.

The validated root grammar is SORTED Eq/D. Soundness covers every accepted
input; completeness is for canonical theorem encodings. It is not a claim
that every padding-slot alias admitted by the sorted parser has a proof.
See report section 6.1 and the unchanged exact canonical-validator control.

MEASURED MODULES (CPython 3.12.14)
--------------------------------
                               tokens  AST  bytes  gzip-9
code/checker_tokens300.py          300  346    626     393
code/checker_ast337.py             310  337    661     401
code/checker_bytes580.py           309  362    580     377

The complete module, including JSON input, validation and ACCEPT output,
is counted. gzip is maximum compression, mtime=0, on normalized source.
gzip is information only; the byte profile's gzip is 2 bytes larger than
its matched 584-byte control. Each measured file imports only the standard
library and has no local runtime dependency. The .py.gz copies decompress
to the corresponding normalized source.

RUN
---
  python3 code/checker_tokens300.py < examples/computation_zero_local.json
  python3 code/checker_ast337.py < examples/computation_zero_local.json
  python3 code/checker_bytes580.py < examples/byte_computation_zero.json

Success means normal exit and exactly ACCEPT plus a newline. Exceptions,
parser failures and other nonzero exits reject. The mathematical semantics
uses finite unbounded resources; an actual Python process has finite limits.

The first two programs consume three-field packets [source,mode,template].
The byte program consumes four-field packets [source,mode,template,major].
The outer input is a JSON array: its last item is the goal, and earlier
items are popped from right to left. Unused integer/list prefixes are
permitted; noninteger data anywhere in the document is rejected.

REPRODUCE
---------
  python3 reproduce.py --verify-manifest
  python3 reproduce.py --metrics-only
  python3 validation/verify.py

The first command remeasures all three checkers and executes the supplied
112 three-field cases for each of the first two profiles, plus 63 four-field
cases for the byte profile. It writes only reproduced/receipt.json.
The independent validation/ suite includes normal and -O runs and a
temporary deliberately invalid diagnostic showing why witness validation
must precede the major proof. The diagnostic is never a usable checker.

BUILD
-----
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Alternatively run python3 build_pdf.py, which handles a missing local TeX format.
Run in this directory; the packaged code/ listings are used by the paper.
Standard AMS, listings, booktabs, hyperref and related LaTeX packages suffice.
No network access is needed for reproduction or PDF rebuilding.

CONTENTS
--------
report.tex, report.pdf    Theory, proofs, comparison, limitations.
code/                    Three measured programs and readable expansion.
examples/                Directly runnable proof certificates.
validation/              Portable canonical compiler and boundary suite.
controls/                Exact old attaining checkers, attributed.
reference/               Frozen upstream mathematical/protocol excerpts.
evidence/                Measurements, audits and verification receipts.
CLAIMS.json              Machine-readable positive claims and unmet goal.
PROVENANCE.json          Commit, incoming archive identities, source origins.
MANIFEST.sha256          Integrity hashes, excluding itself/reproduced/.

PINNED SOURCE
-------------
VladimirReshetnikov/ProveIt
e88ebf229bb61bd870bb229b9c97caaa1e044e6e
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All seven incoming archives at this revision were inspected.
The new Python implementation is not formally verified in Lean or Rocq.
The upstream Lean project was not rebuilt. No repository write was made.
