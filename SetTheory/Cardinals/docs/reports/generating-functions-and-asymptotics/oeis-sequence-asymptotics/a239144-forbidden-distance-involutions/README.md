# Fixed Forbidden Distances in Involutions

A self-contained research article and computational companion, dated 2026-10-02.

## Contents

- `article.pdf` and editable `article.tex`: the complete proofs, explicit first corrections, fixed-distance stabilization, inverse conventions, historical scope, and research questions
- `review.md`: independent mathematical and source-scope review bound to the article source hash
- `code/`: exact symbolic coefficient generation, frontier enumeration, independent subset-count and symbolic checks, sector quadrature, fixed-range/inverse tests, result comparison, and integrity verification
- `expected/`: six reference JSON outputs
- `replay.sh`: portable mathematical replay
- `build_pdf.sh`: optional PDF rebuild from locally installed TeX software
- `requirements.txt`: tested Python dependency versions
- `MANIFEST.json`: complete SHA-256 and size inventory of the distributed payload, excluding the manifest itself

No third-party full papers or unneeded private research records are included. Source links and historical qualifications are in the article. The exact shifted Gaussian matching identity, root-moment technique, and high-order structural-correction method are classical. This companion makes no worldwide-priority claim.

## Integrity and mathematical replay

Extract with Python's standard-library ZIP utility into a new directory, then run Bash explicitly. Execute bits are not required or assumed:

    python3 -m zipfile -e fixed-forbidden-distance-involutions.zip extracted
    cd extracted/fixed-forbidden-distance-involutions
    python3 code/verify_manifest.py .
    bash replay.sh

Python 3.12, SymPy 1.14.0, and mpmath 1.3.0 were used for the checked run. The requirements file pins those library versions. If needed, install them in your own virtual environment using your usual package installation process. No script downloads dependencies or accesses the network. An alternative Python executable can be selected with `PYTHON=/path/to/python bash replay.sh`.

Replay writes to `results/` by default, leaving `expected/` unchanged. Use `OUTPUT_DIR=/some/new/directory bash replay.sh` to choose another output location. The six result files are compared structurally; exact symbolic/rational values must agree exactly, while numerical decimal strings have relative-or-absolute tolerance 1e-40. Quadrature results can depend on mathematical-library versions. All assertions must pass. Logs for each script are retained alongside its generated results.

The universal generator and independent algebra tests cover orders zero through six. The proof and recurrence specify every fixed finite order; order six is the checked computational depth, not an all-orders computation. A fresh subset recurrence checks 120 path-power matching cases and complements. The graph tests cover 1,199 finite examples. These checks support, but do not replace, the analytic remainder proofs.

`verify_fixed_range.py` imports the generator, intentionally repeating its deterministic computations before the fixed-range checks. Runtime therefore includes that extra pass.

## Rebuild the article

With pdflatex, Latin Modern, AMS math, geometry, hyperref, microtype, fancyhdr, booktabs, array, and mathtools locally installed:

    bash build_pdf.sh

This produces `pdf-build/article.pdf`. The script accommodates standard TeX distributions and a restricted-container configuration with locally rebuilt format/font-map data. It does not change global TeX configuration. PDF byte identity across TeX versions or build times is not promised; the distributed PDF itself is hash-pinned. The article's equations and text are the authoritative mathematical deliverable.

## Interpretation limits

Theorems are uniform for each fixed maximum degree and each fixed requested order. Arbitrary graph sequences use their actual n-dependent statistics. Constant coefficients are obtained here for fixed finite forbidden-distance sets, after a proved stabilization result. The weighted approximation is signed and does not imply an everywhere smooth expansion of total-variation distance. Gaussian sectors use an explicit fixed cutoff. The inverse results distinguish smooth roots, exact log-linear interpolation, and integer thresholds; their asymptotic constants are not certified finite-input error bounds.
