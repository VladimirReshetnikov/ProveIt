# Canonical Thue–Morse pressure clusters

This package contains an eight-page mathematical report, its LaTeX source,
portable exact arithmetic checks, and an unchanged companion containing the
previous first-negative theorem and the analytic prerequisites used here.

## Results

For every fixed canonical Schur cluster index k, the report identifies its
leading proportional-degree coefficient asymptotic. The multiplier is the
classical rooted-tree constant (-1)^(k-1) 2 k^(k-1)/k! times
(log_2(2m))^(k-1). The permitted compact saddle window is enlarged by a new
weighted Green estimate on |a| <= 1/2, valid for even d = 2m >= 256.

The appendix characterizes the exact branch-admissibility threshold of this
particular product envelope and certifies a rational bracket for that threshold.
It is not a spectral-singularity assertion.

The cluster index is fixed. The report does not sum all clusters, identify a
later full-pressure sign transition, or assert a uniform Lambert-W approximation.
This is unrefereed ordinary mathematics, not a Lean formalization.

## Files and checks

- article.pdf and article.tex: the report
- checks/check_cluster_algebra.py: exact Lagrange and rooted-tree algebra through k=12
- checks/verify_green_half.py: exact scalar facts and contraction at radius 1/2
- checks/verify_envelope_threshold.py: two exact signs bracketing the unique threshold
- checks/*.json: reproducible exact outputs
- inputs/: unchanged preceding report PDF, TeX and full source archive
- PROVENANCE.json: exact input and file hashes

All new checks require only Python 3 standard-library modules. Run from this directory:

    python -O checks/check_cluster_algebra.py
    python -O checks/verify_green_half.py
    python -O checks/verify_envelope_threshold.py
    python -O verify_package.py

The first three commands replace their corresponding JSON outputs. The threshold
checker imports the scalar checker locally and therefore also replays it.
The finite algebra checks are regressions for the general proof, not substitutes
for it. The scalar rational inequalities certify the stated analytic constants.
No floating-point decision enters these checks.

For a standard TeX Live installation, run pdflatex twice on article.tex. Required
packages are amsmath, amssymb, amsthm, mathtools, geometry, lmodern, microtype,
hyperref and xurl. build_local.sh supplies the explicit font/format setup used
in the preparation environment; no installation or network access is needed.
The bundled input archive has its own portable instructions and certificates.
