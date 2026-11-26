# A counterexample to McNew's natural-density conjecture

Open **report.pdf** for the complete research note. The main result is a set of positive integers avoiding all nonconstant rational-ratio three-term geometric progressions. Its ordinary asymptotic density exceeds Rankin's density by an explicitly certified amount between 1.5728 × 10⁻⁷²⁷ and 1.5730 × 10⁻⁷²⁷. The proof also gives a polynomial-ring analogue for every finite field. The final sections treat a large-field upper bound, a finite central-zero test, and the obstruction to making a fixed number of such samples uniform in the conductor.

## Reproduce the checks

From this directory, run the following with Python 3.11 or later. No external packages are required.

```sh
python3 checks/rankin.py
python3 checks/check_spoke_pairs.py
python3 checks/chowla.py
```

The first program checks local midpoint identities, the simpler integer construction, and the binary polynomial-ring example. The second certifies the stronger construction on 266 primes. Its function `in_example(factorization)` determines membership in the explicit set from an integer's prime factorization. The third program uses outward-rounded decimal intervals for one quadratic Dirichlet character. The corresponding transcripts are in `results/`. The arguments applying to infinitely many integers, all finite fields, or all conductors are given in the manuscript.

## Rebuild the manuscript

A standard TeX Live installation with pdfLaTeX, Latin Modern, and the usual AMS packages suffices. Keep the included TeX source files together and run the following commands.

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

The input sections in reading order are `rankin.tex`, `pair-proof.tex`, `large-fields.tex`, `chowla.tex`, and `optimal-kernels.tex`. The report contains links to the primary papers. `source-map.json` records the GitHub revisions, source locations, and earlier ProveIt reports used for comparison. The Lean verification cited in the report applies to the upstream repository. The new results are supplied as written proofs and reproducible calculations.

The supplied `SHA256SUMS` records all other archive members. To verify the delivered bytes before rebuilding, run `sha256sum -c SHA256SUMS` from this directory.
