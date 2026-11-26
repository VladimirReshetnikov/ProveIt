# Prime-exponent patterns and p-adic branch precision

Open **report.pdf** for the research note. The first part gives a one-digit counterexample to McNew’s Conjecture 7.2 and classifies all replacements deleting at most two patterns. It proves a uniform obstruction for bounded prime blocks and verifies Rankin optimality through width four. The second part answers a question about sampling Lubin–Tate branches modulo powers of the uniformizer and applies it to explicit congruences of integer binomial sums.

## Build and replay

Use a conventional TeX Live installation and run `latexmk -pdf report.tex` in this directory. The section sources, bibliography and all mathematical definitions are local. For the exact checks run `python3 verify.py` with Python 3.10 or later. It runs eight standard-library scripts with assertions enabled and compares their outputs with the files in `results/`. No solver, Lean installation or network connection is required. The program with the largest search enumerates 5,787,763 branch nodes across 171 rectangular prefixes.

## Source record

The two Git commits, the Lean and mathlib versions and Git blobs of selected source files and earlier reports are recorded in `sources.json`. The bibliography and source discussion distinguish inherited results, classical cases and the contributions of this note. These extensions consist of mathematical proofs and standalone finite computations. The authors of the upstream repository report checking its proof with Lean; this package does not contain a new Lean certification.

The SHA-256 manifest covers the PDF, sources, scripts, expected outputs and this README. To check the extracted files, run `sha256sum -c SHA256SUMS`.
