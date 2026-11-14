U208 research release, 29 October 2026

Result: two 208-working-state binary blank-tape machines. The primary is
machine/u208.tm; the secondary is machine/variant_plain/u208.tm.
Each dense table has working labels 0..207, halt 208, start 0, head 0,
all-zero bi-infinite tape, and only L/R moves. Native labels are historical.
The ordinary mathematical proof transports the PA-provable Con(U) endpoint
from the supplied parent; this is not a newly exported proof-assistant
certificate or a minimum-state claim. The new fold may slow computation.

Read report/report.pdf or edit report/report.tex.
Run from the extracted root (Python 3.10+):
  python3 verify.py --output /tmp/u208-finite.json
  python3 -O verify.py --output /tmp/u208-finite-optimized.json
  python3 verify.py --full --output /tmp/u208-full.json
The full check covers both new tables, 5,084 universal symbolic contracts
per table. It requires enabled assertions; optimized full runs are rejected.
  python3 build_report.py --source report
TeX rebuilding requires pdflatex and the indicated standard packages.
Rebuilding may change PDF metadata while preserving page content.

Supplied upstream programs are evidence, not executed by these commands.
The runtime engine is exact-hash-bound, self-authored prior infrastructure.
The compact selection retains theory/proofs, licenses and provenance,
including the previously delivered U212 dependency ZIP. Large duplicate
archives, case dumps and duplicate PDFs are omitted with hash ledgers.
MANIFEST.json binds the release payload. The standalone verification receipt
records the sealed-extraction replay and PDF checks without self-reference.
