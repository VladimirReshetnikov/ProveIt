# Finite observations of arithmetic Levy paths and critical recovery of symplectic forms

Research note prepared for Vladimir Reshetnikov, 27 November 2026.

This archive contains two proved extensions of the ProveIt GRH research
programme, their complete LaTeX sources, the compiled report, verification
programs, numerical outputs, and provenance records.

## Main results

1. **Arithmetic identification from noisy positions.** A fixed observation
   interval of a Dirichlet Li--Levy process permits recovery of any fixed finite
   set of real prime character values from increasingly fine position samples.
   The position errors may be chosen adversarially after seeing the path; every
   known error bound tending to zero is admissible after an appropriate
   bandwidth choice. The report proves explicit mean-square bounds, a joint
   Gaussian limit, a finite-sample confidence inequality with specified input
   constants, and identification within any fixed finite candidate family.
   Fixed-order mesh correction gives achieved error exponents approaching one
   quarter. This result uses the repository's Dirichlet-GRH input and its
   arithmetic explicit formulas.
2. **The full linear critical window for a hidden symplectic form.** At
   `t = n(n-1)/2 - 1 + a` random two-plane observations, the linear solution-space
   dimension has an explicit limiting distribution under both the null and
   planted models. The result gives limiting linear-recovery probabilities,
   optimal tests that use only solution-space dimension, and the distribution
   and moments of the extra observations needed for a one-dimensional solution
   space. It holds over every fixed finite field and is unconditional.

The report distinguishes linear uniqueness from uniqueness restricted to
nondegenerate forms, and dimension-only testing from testing using all the
observations. Neither new theorem has been formalized in Lean. The comparison
with the inspected repository and literature establishes a scoped extension;
it does not assert worldwide publication priority.

## Contents

| Path | Purpose |
| --- | --- |
| `finite_observation_and_critical_recovery.pdf` | Complete readable report and proofs. |
| `finite_observation_and_critical_recovery.tex` | Main LaTeX source. |
| `sections/` | Source analysis, analytic theorem, finite-field theorem, verification notes, and references. |
| `figures/critical_profiles.pdf` | Vector figure of the proved limiting recovery and testing curves. |
| `figures/critical_profiles.png` | Raster copy of that figure. |
| `code/noisy_path_decoder.py` | Floating-point implementation of the first-order position estimator. |
| `code/verify_hidden_forms.py` | Exact finite-field checks, exact binary finite-size laws, limiting profiles, and reproducible Monte Carlo experiments. |
| `code/verify_analytic_algebra.py` | Exact extrapolation checks and a deterministic decoder implementation check. |
| `results/` | Complete numerical and exact-check outputs, plus environment versions. |
| `provenance.json` | Pinned sources, inspection scope, earlier hidden-form note hash, and validation scope. |
| `provenance/verified_article_manifest.json` | Git blob hashes and SHA-256 hashes for 39 retrieved Article source files. |
| `requirements.txt` | Exact NumPy, SciPy, and Matplotlib versions used for the computations. |
| `Makefile` | Convenience targets `make pdf` and `make verify`. |
| `SHA256SUMS` | Checksums of all other packaged files, before any regeneration. |

## Rebuild the PDF

Run from this archive's top directory, with a TeX distribution providing the
standard packages named in the main source:

```bash
pdflatex -interaction=nonstopmode -halt-on-error finite_observation_and_critical_recovery.tex
pdflatex -interaction=nonstopmode -halt-on-error finite_observation_and_critical_recovery.tex
```

The bibliography is included in `sections/references.tex`; no BibTeX run or
repository checkout is required. The included vector figure is sufficient for
the PDF build. To regenerate that figure, run the hidden-form verification
program first.

The equivalent convenience command is `make pdf`.

## Reproduce the computations

Python 3 with NumPy, SciPy, and Matplotlib is needed. Exact preparation versions
are recorded in `results/environment.json`. The exact incidence computations
use Python integers and `fractions.Fraction`; the decoder and plotted products
use floating-point arithmetic.

To install the three pinned computational dependencies in your chosen Python
environment, run `python3 -m pip install -r requirements.txt`. The preparation
environment used Python 3.12.14.

```bash
python3 code/verify_hidden_forms.py --repetitions 5000
python3 code/verify_analytic_algebra.py
```

The scripts locate their output directories relative to their own files. The
commands overwrite the corresponding files in `results/` and regenerate the
two critical-profile figures.

The equivalent convenience command is `make verify`. Its default is 5,000
Monte Carlo repetitions; `make verify MC_REPETITIONS=1000` selects a shorter
illustrative run while retaining the same exact checks.

The hidden-form program performs these checks in one run:

- Enumerate all two-planes and alternating forms on `F_2^4` and `F_3^4`, checking
  1,586 null/planted Fourier identities exactly.
- Compute exact binary nullity laws for `n=4` through 12 observations by dynamic
  programming on the actual row spaces.
- Evaluate the limiting products, recovery curve, dimension-testing curve, and
  stopping-time moments.
- Generate 5,000 trajectories **per model and dimension**, for the null and
  planted models at `n=6,10,14`, with seed `20261127`. The same trajectories
  supply offsets `a=-2,...,5`; this is 30,000 trajectories in total.

The exact enumeration program implements field arithmetic only at the prime
fields `q=2,3`. The figure also includes `q=4` by evaluating the proved scalar
product formulas, without pretending to implement extension-field arithmetic.
Monte Carlo comparisons are illustrations containing sampling error and
finite-size effects; the mathematical proofs do not rely on those comparisons.

The analytic program verifies the extrapolation identities and allocation
factors for correction orders 1 through 8. Its three-jump example checks signs,
normalization, and angle inversion. That example is a synthetic finite-jump
path, not a simulation of a Dirichlet Li--Levy process.

## Use the position decoder

Supply a JSON file, such as `samples.json`, with these fields:

| Field | Meaning |
| --- | --- |
| `positions` | Array of `n+1` finite real position readings in time order. |
| `time_step` | Positive uniform mesh `h` between consecutive readings. |
| `level_noise_bound` | Optional nonnegative bound on each position error; default zero. |

Then run:

```bash
python3 code/noisy_path_decoder.py samples.json --primes 2 3 5
python3 code/noisy_path_decoder.py samples.json --primes 2 3 5 --bandwidth 20
```

The automatic bandwidth is
`min(h^(-1/4), (2*level_noise_bound)^(-1/3))`, with the second term omitted
when the error bound is zero. The implementation requires a bandwidth at least
two and reports an error if the automatic asymptotic regime has not reached
that point. The position-error bound is doubled to bound increment errors.

Output is JSON containing the estimated real character values, selected
bandwidth, observation duration, selected increments, asymptotic standard
deviation scales, and the two quantities appearing in the theorem's CLT
conditions. The implementation needs no zero table, conductor, or candidate
character. It implements the first-order estimator; higher-order extrapolation
is proved and its identities are checked, but is not exposed as a decoder CLI.

The reported standard deviations and CLT diagnostics are not certified
finite-sample confidence intervals. A certified implementation would additionally
need controlled transcendental evaluation and numerical bounds for the
model-specific quantities in the report's confidence inequality. The report
also gives the deterministic contribution of probe-evaluation error.

## Source and verification scope

The repository snapshot is
`VladimirReshetnikov/ProveIt@7c24c5481fc0c8101b22b7e7cfab8321921c0faa`.
The upstream Dirichlet-GRH input is
`lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`.

The current Article catalogue, source theorem, and relevant source modules were
examined, with detailed mathematical attention to the exact-jump decoder,
rational-frequency estimates, and symplectic observation models. The 39-file
manifest records retrieved and hash-verified material; it is not a claim that
every proof in the 895-page merged article was independently audited. The
relevant earlier hidden-form working copy is separately identified and hashed
in `provenance.json`. The full upstream Lean development was not rebuilt here.

Separate internal reviews checked the written proofs, and the finite checks
were run as described above. The archive contains no new Lean proof. In particular,
the higher-order analytic theorem supplies mean-square bounds, not a sharp CLT
throughout its enlarged bandwidth range. Conductor-uniform inference constants,
optimal statistical rates, the number of compatible nondegenerate forms, and
full-data optimal testing remain outside the established conclusions.
