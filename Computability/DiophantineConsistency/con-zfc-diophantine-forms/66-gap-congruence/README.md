# Gap coordinates, congruence norms, and direct proof certificates

Research contribution for ProveIt, based on commit
beb0192cb8dc36f78c369c080f2adfbc1887a486 (23 October 2026).

Start with `report/report.pdf`. The editable source is `report/report.tex`.
Completed ordinary polynomial equations and exact circuits are in `nine/`,
`integer/`, and `algebra/`. Their unknown domains are not interchangeable.
The direct one-stack source in `direct/` is a local polynomial and an explicit
uncompiled global constructor proposal, NOT a completed small consistency
equation. It avoids K215 and Jones at the source level.

Run `python verify.py` from a clean extraction. Python 3 and SymPy are needed.
The driver checks all sealed hashes, matches retained source bytes, creates
an isolated copy, runs only authored checks/builders, and compares generated
circuit files byte for byte. Run `python negative_controls.py` for corruption
controls. Build the PDF with `bash report/build.sh` using a standard TeX Live
installation (pdflatex, lmodern, microtype, hyperref, xurl).

All coefficients in the delivered completed circuits are literal signed
integers stored losslessly as binary gzip payloads. Fixed numeral construction
is excluded from arithmetic operation counts; live arithmetic on unknowns
is counted. No running-time, bit-complexity, global-minimality, consistency
proof, or new end-to-end Lean/Rocq verification claim is made.

`review/` preserves intake receipts and source pins for all six incoming
contributions. Incoming programs were never executed or imported. Only inert
source data and proofs needed for this release are retained; the original
archives are linked by pinned Git identities. `PROVENANCE.json` maps retained
byte-identical members, and `SHA256SUMS.json` seals the complete deliverable.
