# Two continuations of the ProveIt GRH program

Research package prepared for Vladimir Reshetnikov on 27 November 2026.

Source revision: `3413bfb1edb3636437f9cec7e5dd975869f7d120` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/3413bfb1edb3636437f9cec7e5dd975869f7d120/Analysis/GeneralizedRiemannHypothesis).

## Main papers

| File | Result |
| --- | --- |
| `finite_population_parity.pdf` and `.tex` | For every sequence of block capacities at least two, the complete parity vector of a uniform fixed-size sample is asymptotically equivalent to biased independent signs conditioned on their global product, provided the parity bias tends to zero. This gives an exact capacity-dependent Gaussian distance profile and a source-dependent corollary for many simultaneous prime products. |
| `five_observation_recovery.pdf` and `.tex` | Any two distinct normalized five-point response shapes jointly recover the limiting spectral count. The paper gives an exact three-line criterion for a uniform joint symbol gap, the unique infinitely blind normalized shape, all its positive anti-periodic tangent measures, and finite dilation repairs. |

Both papers contain full mathematical proofs, figures, references, and explicit hypotheses. The first paper is the principal probability contribution. The second continues the zero-statistics and finite-contrast branch of the source project.

## What is new, and what is inherited

The contributions above were not found in the inspected merged article and relevant incoming reports. This is a bounded source and literature assessment, not a guarantee of historical priority.

The incoming report **The missing frequencies of five-point prime variances** already proves the five-point quadratic/phase classification, the bound of two missing positive frequencies, and attainment of that bound. Our second paper credits and restates those results. Its distinct additions are the universal two-shape theorem, exact joint separation criterion, and complete tangent theory; its rational certificate supplies an explicit independent witness, not the first existence proof.

The incoming report **Every sparse prime-product transition is compound Poisson** concerns one sparse sampled product in a bounded quotient. Our first paper concerns a growing-dimensional joint parity vector and allows fixed capacities and dense sampling. The classical Gaussian profile for hypercube walks, the source's bounded-quotient reduction, and the source's fixed-block entropy calculation are all credited as predecessors.

See `PROVENANCE.txt` and `verification/five_point_novelty_audit.txt` for precise source boundaries.

## Mathematical and formal status

- The finite-population theorems and all analytic contrast/tangent theorems are unconditional.
- The prime-variance interpretation uses RH and the stated explicit formula.
- The simultaneous prime-product corollary uses Dirichlet GRH and the source's `dir:thm:disjoint-growing`; that arithmetic lifting theorem is explicitly an input.
- These are ordinary mathematical proofs. They are **not newly Lean-checked theorems**, and the included internal reviews are not external peer review.
- The upstream RH/Dirichlet-GRH build and independent proof-checker reports were inspected as sources; their builds were not rerun for this package.
- The spectral recovery result does not assert convergence of the actual squared-multiplicity statistic, simplicity of zeta zeros, or realization of the abstract countermodels by an Euler product.
- The uniform joint gap concerns the finite symbols. It is not an error bound for noisy finite-height Mellin inversion.

## Rebuild the PDFs

Use Python 3.11 or newer and a TeX distribution containing `pdflatex`, Latin Modern, AMS packages, `microtype`, `mathtools`, `enumitem`, and `hyperref`. `latexmk` is preferred; the build script falls back to two `pdflatex` passes.

From this directory:

```bash
python3 build.py
```

The included figures are sufficient for rebuilding the PDFs. To regenerate the calculations and figures as well:

```bash
python3 -m pip install -r requirements.txt
python3 build.py --check
```

Individual commands are:

```bash
python3 checks/certify_double_blind.py verification/double_blind_certificate.json
python3 checks/verify_symbols.py
python3 checks/verify_parity.py
python3 checks/plot_shapes.py
```

The exact existence certificate needs only Python's standard library. Symbol checks use SymPy. Numerical illustrations use NumPy and Matplotlib.

## Verification artifacts

- `checks/certify_double_blind.py`: rational interval arithmetic, logarithm and trigonometric remainder bounds, and a Banach fixed-point certificate for a genuine five-weight contrast with exactly two blind positive frequencies. No floating-point value participates in a proof assertion.
- `checks/verify_symbols.py`: exact symbolic checks of the five-point response, symbol, elimination identity, exceptional corners, and special dyadic kernel identity.
- `checks/verify_parity.py`: exact integer coefficient extraction and exact total variation from the uniform parity fibre. It checks 56 small parameter cases by exhaustive subset enumeration and records 95 larger examples. Gaussian and conditioned-independent comparisons are floating-point diagnostics.
- `verification/*.json`: reproducible results of the checks.
- `verification/*audit.txt`: internal mathematical and source-overlap reviews, with formal-status limitations.
- `figures/`: vector PDF and raster PNG versions of both research figures, regenerated by the supplied scripts.
- `MANIFEST.sha256`: checksums of all delivered files except the manifest itself.

The finite computations support specific identities and examples. The asymptotic theorems are proved in the manuscripts; their proofs do not rest on the plotted numerical agreement.
