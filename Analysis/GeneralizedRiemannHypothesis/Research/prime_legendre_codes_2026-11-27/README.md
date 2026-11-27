# Prime-labelled codes with two-sided Gilbert–Varshamov distances

Research note, 27 November 2026. Intended for possible integration into ProveIt's `Analysis/GeneralizedRiemannHypothesis` research collection. No GitHub files were changed.

## Results

- With two disjoint families of distinct primes bounded by `O(n^2 log^2 n)`, the binary Legendre-symbol matrix generates a rate-R code whose primal and dual relative distances exceed any fixed targets strictly below their respective Gilbert–Varshamov thresholds. Every submatrix can simultaneously have rank defect less than any prescribed positive fraction of n.
- Primes bounded by `O(n^(2+eta))` allow both distances to approach their thresholds and give uniform rank defect `O(n/log n)` across all rectangles.
- Fixing the row primes to the first r odd primes still permits the simultaneous distance and rank guarantees, using column primes in a window at scale `r^3 (log r)^4`.

The asymptotic theorems use Dirichlet GRH exactly as exported by the vendored Lean development; their proofs are ordinary mathematical proofs. The upstream formal proof was inspected but not independently built, and the downstream argument has not been formally checked in Lean. No claim to improve the unrestricted GV bound, prove optimal cutoffs, or establish publication priority is made.

## Files

- `prime_legendre_codes.tex`, `prime_legendre_codes.pdf`: self-contained mathematical report with proofs, finite probability estimate, asymptotic results and source discussion.
- `verify.py`: standard-library exact finite-code verifier and reproducible example generator.
- `examples.json`: actual primes, binary matrices, complete primal and dual weight enumerators, and exhaustive rectangle-rank certificate for the smallest code.
- `examples_summary.csv`, `checks.txt`: compact table and actual verification output.
- `sources.md`: provenance, selected source identifiers, and comparison scope.
- `formalization.md`, `PrimeCodeInput.lean`: explicit Lean integration plan and uncompiled adapter to the existing GRH theorem (not a formalization of the new result).
- `SHA256SUMS.txt`: hashes of all other shipped files.

## Reproduction

From the extracted folder, execute:

```sh
python3 verify.py                 # recompute and compare all exact certificates
python3 verify.py --regenerate    # regenerate the example search and certificates
pdflatex -interaction=nonstopmode -halt-on-error prime_legendre_codes.tex
pdflatex -interaction=nonstopmode -halt-on-error prime_legendre_codes.tex
sha256sum -c SHA256SUMS.txt         # check original shipped bytes before regenerating
```

Python 3.10+ recommended. The exact finite checks require neither Lean nor GRH. They do not verify the asymptotic theorem; they demonstrate the construction and validate finite certificates. LaTeX uses standard packages and no external bibliography processor. The example search uses a fixed pseudorandom seed and an exact integer sampler; results selected from several trials are not statistical estimates of the success probability. The theoretical constants and sufficiently-large-n thresholds are not numerically optimized.
