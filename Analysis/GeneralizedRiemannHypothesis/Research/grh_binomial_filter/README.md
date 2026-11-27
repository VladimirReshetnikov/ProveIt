# A constant-free binomial filter for prime discrepancies

Research note, 26 November 2026.

## Contents

- `paper.tex`, `paper.pdf`: full theorem, proofs, related literature, generalization to subgroups, exact low-frequency annihilation, and further questions.
- `experiment.py`, `experiment.csv`, `experiment.log`: numerical finite prime-power tests and the recorded run (60 rows). The Python code requires NumPy; it uses the sieve of Eratosthenes, all prime powers and extended-precision prefix sums. Values are illustrative, not certified intervals.
- `FORMALIZATION.md`: proof dependencies and a proposed Lean integration plan, not a completed formalization.
- `SOURCES.md`: exact GitHub pin, inspected paths, literature and claim-scope distinctions.
- `SHA256SUMS`: checksums of these files.

## Reproduction

From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python experiment.py
sha256sum -c SHA256SUMS
```

Running the experiment may produce platform-dependent last digits because NumPy's `longdouble` precision varies. Run the checksum command before regenerating files if checking the original archive's integrity. The default sieve cutoff is 12,744,840. The script rejects cutoffs above 50 million to limit resource usage.

## Scope

The forward theorem follows from Dirichlet GRH as stated in the supplied Lean repository; the fixed-depth one-sided converse is unconditional. The proof does not require the extended GRH for Dedekind or general automorphic L-functions. The result is a candidate original construction; priority has not been established by an exhaustive literature review. The repository itself was inspected via GitHub at the pinned commit, not rebuilt locally. No Lean verification of this new paper is claimed, no explicit numerical rounding threshold is established, and no repository files were changed.
