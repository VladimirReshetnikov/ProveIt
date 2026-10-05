# Reader validation summary

**PASS: exact algebra and declared finite checks.** Python 3.12.14, SymPy 1.14.0. Ordinary and optimized (`python -O`) runs produced identical mathematical summaries. No check relies on Python `assert` statements or floating-point tolerances.

## Coverage

- Both rational kernels, stochastic/color normalization, phase drifts and mean-zero Poisson correctors
- Effective covariance by two constructions: corrected-increment moments and the log-Perron-root Hessian; separate phase-conditioned covariance matrices
- Exact exponential certificates at `exp(t)=6/5`: corner quotient-displacement moment `524/405`; Schnyder aggregate physical-length moment `189/13`
- Positive-support Fourier witnesses with a unimodular integer character matrix
- Symbolic forward and dual quadrant seeds for every integer `H >= 1`, including every intermediate edge and phase
- Exact endpoint tilt factors and size shifts; independent rational-kernel/original-walk endpoint counts through time 12
- All 32 recorded A377922 terms and all 31 recorded A377920 terms; a safe corner fixed-endpoint budget through time 32
- A377921's 16 recorded terms, 31 coefficients reconstructed from the full formal generating-function identity, positive convolution/window checks at indices 4–30, and 151 exact first-crossing probes covering every breakpoint/open cell in the stated finite range
- Sleeve local color rules for zero or arbitrary positive old boundary degree, canonical labels/bipartition, annular graph and all six facial 4-cycles, root recovery and inverse deletion, Euler/size increment, and the six-shift count comparison at indices 8–30
- Exact angle intervals giving `4 < alpha_P < 5` and `6 < alpha_S < 7`; exact nonintegral rational twice-cosines for the algebraic-integer irrationality argument

## Adversarial and replay evidence

All **57 named mutants** were rejected under `python -O` with their declared diagnostics: **47 mathematical** and **10 schema** mutations. A traceback, syntax-only failure, timeout, wrong diagnostic or unaltered fixture would fail the campaign. Every mutant has a recorded baseline/mutated fixture SHA-256 pair. Baseline source hashes were actually read before and after and remained equal.

A fresh temporary directory received byte-identical copies of the six validation inputs. It repeated ordinary and optimized runs and all 57 mutants successfully. The supplied machine-readable records are:

- `results/validation_manifest.json`: baseline modes, every mutant and diagnostic, hashes and fresh replay status
- `results/fresh_replay_manifest.json`: the complete independent-directory rerun
- `results/ordinary.json` and `results/optimized.json`: exact mathematical outputs, ranges and exclusions
- Corresponding `.log` files: concise successful-run transcripts

## Limits

The corner convention `p_0=0`, exceptional Schnyder values at indices 0–3 and the auxiliary two-SE initialization `r_0=1` are explicitly distinguished from general-size enumerated combinatorial objects. Recorded OEIS prefixes are offline fixtures; current live-page completeness is not certified.

Finite checks do not prove the cone theorem, FCLT, unrestricted/killed LLT, general-map sleeve injectivity, asymptotic transfer, G-function/non-D-finiteness argument, inverse asymptotics or full multiplicative equivalents. The report supplies the relevant mathematical proofs. In particular the all-n A377921 conclusion uses the written sleeve injection and analytic A377920 result; it is not extrapolated from finite coefficients.

## Reproduce

From the report directory, run `python3 checks/validate.py`, `python3 -O checks/validate.py`, and `python3 checks/run_validation.py --output tmp/local-check-results`. The last form leaves the supplied evidence unchanged. See `checks/README.md` for detailed methods and provenance.
