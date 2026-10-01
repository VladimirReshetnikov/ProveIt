# First negative degrees in integer Thue–Morse pressure

The article proves the asymptotic location of the first negative even phase Taylor coefficient above the cancellation at degree 2m:

    N_m = gamma*m - loglog(2m)/Lambda + O(1)

The constants are defined by a positive-series saddle equation. Exact rational checks place gamma strictly between 6.662966 and 6.662968, below 20/3. The coefficient 1/Lambda is approximately 1.240284909.

A further corollary gives the next-even-integer rule for an explicit saddle center when that center is outside an existential C/log(2m) neighborhood of the even lattice. The report gives no effective onset, no unconditional exact floor rule, and no claim about the frequency of close lattice approaches.

This is an unrefereed ordinary mathematical proof with exact compact-domain interval certificates, not a Lean formalization. Finite first-negative tables are supplementary and are not used to infer the theorem.

## Read the proof

- `article.pdf` and `article.tex` contain the complete new analytic argument and describe every imported estimate
- `inputs/all_integer_orders.pdf` and its unchanged source archive supply the weighted C1 Green theorem, dyadic tangent comparison and earlier all-order positivity result
- `inputs/eventual_66.pdf` and `.tex` supply positivity at all earlier degrees for sufficiently large orders and the third-Schur-term bound
- `inputs/infinite_sign_changes.pdf` supplies existence of N_m
- `inputs/repository_integer_pressure.tex` is the pinned repository source
- `inputs/independent_outer_certificate.zip` is a separate portable replay bundle for the outer contour, copied unchanged

## Replay the exact certificates

The new checkers need only Python3 and its standard library. No network access or third-party package is needed. Run from the package directory:

    python3 -O checks/verify_model_crossing.py
    python3 -O checks/verify_contour_side_conditions.py
    python3 -O checks/verify_frozen_real_constants.py
    python3 -O checks/verify_local_complex_arc.py
    python3 -O checks/verify_sharp_certificate.py

The first also replays the preceding 6.6 endpoint checks. The local checker certifies 127 rational boxes with strict domain slack. The compact outer replay reconstructs the exact binary partition and checks all 2812 boxes, proving eta=1999/2000. Its runtime is about one minute on the production system. All failure checks remain active under Python's optimization flag.

Optional regeneration of the compact outer partition:

    python3 -O checks/produce_sharp_outer.py

Regeneration rewrites the certificate, with elapsed timings that may differ. Mathematical bounds and the deterministic partition are unchanged. Validate SHA256SUMS before regeneration if checking the original archive identity.

The independent outer ZIP contains a separate saved-leaf replay and saddle-range check. Its README gives the two commands. The logarithmic spatial derivative proof is included there.

## Build the paper

A standard TeX Live installation with pdfLaTeX, AMS packages, geometry, Latin Modern, microtype, hyperref and xurl can compile `article.tex`. The included `build_local.sh` performs two passes and also supports the explicit TeX/font paths used in production.

The asymptotic proof uses a uniform local limit theorem; no finite list of coefficient checks replaces that argument. Conversely, the finite interval boxes certify only the compact scalar inequalities, whose operator and coefficient consequences are proved in the article.
