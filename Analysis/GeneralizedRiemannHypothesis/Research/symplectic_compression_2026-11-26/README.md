# Exact symplectic compression laws

Research prepared for Vladimir Reshetnikov, 26 November 2026.

## Start here

- `paper.pdf`: complete 13-page mathematical paper (the final page count is also recorded in `results/document_validation.json`).
- `paper.tex` and `sections/*.tex`: all LaTeX sources.
- `code/compression.py`: exact probability and overlap calculator.
- `code/minimal_realization.py`: deterministic realization in the smallest possible symplectic ambient space.
- `results/`: recorded exact checks and example certificates.
- `provenance/`: upstream audit, predecessor and literature comparison, source identifiers, and independent proof review.
- `formalization_blueprint.md`: proposed formal proof dependencies; no compiled Lean development is claimed.

## Main results

For arbitrary prescribed alternating Gram forms H1,H0 and cross matrix A, form

    Gamma = [[H1,A],[-A^T,H0]].

Write rank(Gamma)=2s, let r be its radical dimension, and let ti be the radical's intersection dimension with coordinate block i. The paper gives an explicit nonnegative integer coefficient T_l counting relation spaces that meet neither block. Multiplying T_l by the classical number of injective realizations of the quotient gives the joint law of the complete observed matrix and the intersection dimension of the two frames.

The exact minimum ambient dimension realizing all pairings while preserving injectivity of each frame is

    2 * (s + max(t0,t1)).

For fixed field and fixed frame sizes, the full distribution differs from independent uniform entries by a sharp positive leading term of order q^(-2n), where the ambient dimension is 2n. The paper computes that term explicitly. It also gives a closed two-plane law and an optimal determinant-one test.

The theorem holds over every finite field, including characteristic two. Its proof is unconditional. It extends the exact finite-field compression results in the supplied ProveIt collection; it does not assert an additional Riemann hypothesis. The targeted literature comparison did not locate the combined theorem, but worldwide publication priority has not been established. Classical ingredients are credited in the paper.

## Reproduce the exact computations

All evaluators and verification programs require Python 3.10 or later and only the standard library. From this directory:

```bash
bash verify.sh
```

This reruns two independently implemented direct-frame enumerations, an independent enumeration of transverse radical subspaces, exact integer-polynomial checks of the asymptotic formulas, and constructive minimal-realization tests. It records outputs under `results/` and stops on any failed assertion. No random seeds or numerical tolerances enter these checks.

For one exact probability:

```bash
python3 code/compression.py code/example_matrix.json
```

The input keys are `q`, `n`, `H1`, `H0`, and `matrix`; arrays are row-major. The example is q=3, ambient dimension four, two symplectic planes, and observed matrix I2. Its probability is 11/720, its density relative to uniform entries is 99/80, and conditional overlap dimensions one and two have probabilities 32/33 and 1/33.

For a smallest realization:

```bash
python3 code/minimal_realization.py code/example_realization.json
```

This constructor accepts `q`, `H1`, `H0`, `M`, and optional `n`. Without `n`, it constructs the minimum dimension; a larger `n` adds unused symplectic coordinates. The output contains frames `F1`, `F0`, ambient form `J`, a relation basis, and exact rank and Gram certificates. This is a deterministic maximal-overlap construction, not a uniform sampler.

### Finite-field implementation scope

The calculator and constructor support every prime q and the explicit field F4=F2[x]/(x²+x+1). For q=4, integer labels 0,1,2,3 mean 0,1,x,x+1; addition is XOR. Other extension fields require a proper field implementation. The programs reject unsupported q rather than use arithmetic modulo a composite integer. The abstract theorem is valid for all prime powers.

## Rebuild the paper and figure

On a standard TeX Live installation:

```bash
bash build.sh
```

The archive already includes the vector figure and the compiled PDF. To regenerate the figure, install the optional packages in `requirements.txt` and run:

```bash
python3 code/make_figure.py
```

The figure is computed from exact finite formulas, not simulation. Local infrastructure details used for the delivered PDF are recorded in `results/document_validation.json`.

## Pinned sources

- grh-lean: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- ProveIt: `041d8032541746f2ac2e686fbe437f8092771670`.
- Closest predecessor archive, symplectic rank blindness: Git blob `ec19f1ebda1c32ab29b3bc00575962b411c73b7c`.

The 48 later incoming archives were checked against their Git blob identities before inspection. The source manifest and audits document the scope of that comparison. The new proofs have been independently rederived and computationally checked in the finite cases listed above; they have not undergone external peer review or Lean formalization.

## Integrity

`SHA256SUMS.txt` records the SHA-256 digest of every other deliverable member. Temporary build files and Python bytecode are omitted from the archive.
