# The first return to positive coefficients in integer Thue–Morse pressure

Let N_m be the first even degree above 2m with a negative pressure coefficient,
and M_m the first later even degree with a strictly positive coefficient.
The report proves, as m tends to infinity,

    M_m = 2 sigma_* m - log(log(2m))/Lambda_* + O(1),
    5.572505 < sigma_* < 5.572507.

A uniform three-model law near this transition has leading multipliers 2,
-2 log_2(2m), and 3(log_2(2m))^2. A certified two-model bridge excludes an earlier
return after N_m. A refined next-even-degree conclusion is conditional on
separation from an O(1/log m) neighborhood of the even lattice.

The onset is not effective. No claim is made about still later transitions or
an unconditional exact floor rule. This is unrefereed ordinary mathematics with
exact rational scalar certificates, not a Lean formalization. No exhaustive
priority claim is made.

## Included files

- article.pdf and article.tex: the complete new report
- checks/: portable exact scalar, product, corridor, model-rate and contour checks
- checks/**/*.json: reproducible rational certificates
- run_checks.sh: replays all new checks with Python optimization enabled
- inputs/: unchanged canonical-cluster and first-negative reports
- inputs/canonical_clusters_sources.zip: unchanged source archive and earlier inputs
- PROVENANCE.json and verify_package.py: file and dependency integrity checks

The new report supplies the boundary-layer norm, principal renewal argument,
entire template, positive arctangent representation, contour integration and
negative bridge. The included first-negative Proposition 7.1 supplies the refined
first-transition lattice window. The canonical-cluster source archive includes
its complete source archive, pinned repository normalization and earlier
analytic prerequisites.

## Reproduce the finite certificates

Only Python 3 standard-library modules are required. From this directory run:

    bash run_checks.sh
    python -O verify_package.py

Every acceptance test uses exact directed arithmetic and explicit exceptions.
The checkers regenerate their JSON output. Decimal values printed in some
scripts are orientation only. The general operator and asymptotic arguments
are mathematical proofs; finite scalar checks do not replace those arguments.

The checks cover the full-envelope inverse, model saddle ranges, connected
two-pulse bounds, 576 corridor derivative cells, 81 corridor modulus cells,
spiral constants, exact second/third crossing, the outer-circle certificate,
215 bridge phase cells and 201 enlarged shallow-template boxes. The arctangent
logarithmic representation and the uniform phase curvature are proved in the
article. All finite domain partitions are reconstructed rather than sampled.

## Rebuild the PDF

A standard TeX Live installation can run pdflatex twice on article.tex. Packages:
amsmath, amssymb, amsthm, mathtools, geometry, lmodern, microtype, hyperref and xurl.
The supplied build_local.sh records the explicit font/format setup used in the
preparation environment. No package installation or network access is needed.
