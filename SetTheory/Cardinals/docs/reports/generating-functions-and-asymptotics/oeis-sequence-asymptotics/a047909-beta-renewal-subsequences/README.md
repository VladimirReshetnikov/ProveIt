# Quantitative Beta renewal asymptotics

Research article and reproducibility materials for complete increasing subsequences in multiset permutations, OEIS A047909 and its diagonal A268485.

## Start here

Read `beta-renewal-asymptotics.pdf`. The editable source is `beta-renewal-asymptotics.tex`.

The article gives a uniform central expansion at every fixed finite order, explicit first four central polynomials, four diagonal half-integer corrections with a parity proof, smooth probability and count inversions with integer-rounding qualifications, and all fixed integer orders for rare success/failure when the exact ratio k/m stays in a compact set separated from 1. It includes self-contained proofs and further research questions.

The Beta renewal identity and Gaussian limit are established El Maazouz–Pitman results. This report does not claim to newly solve the older Gaussian or moment conjectures. Novelty statements are bounded by the source search described in `SOURCES.md`; general Edgeworth and saddle methods are not claimed as new.

## Replay

Requirements: Python 3.10 or later, Bash, SymPy 1.14.0, and mpmath 1.3.0. The checked package versions are pinned in `requirements.txt`.

After extracting the ZIP, run:

    python3 -m pip install -r requirements.txt
    bash replay.sh

The replay itself is offline and does not install anything. The installation command, if needed, requires package-registry access. An already provisioned environment needs no network.

To compile the PDF too:

    bash replay.sh --with-pdf

PDF compilation needs a working pdfLaTeX distribution with the packages listed in the TeX preamble, including Latin Modern, microtype, amsmath, amsthm, mathtools, geometry, booktabs, enumitem, hyperref and fancyhdr. `build.sh` includes a Debian fallback for an unpopulated TeX filename database and builds a local format when needed. Invoke both shell entry points with Bash; no executable permission bits are required. Override the Python executable with `PYTHON=/path/to/python` if needed.

`replay.sh` checks `SHA256SUMS`, copies the Python scripts to a fresh replay area, runs all checks, and compares regenerated data with the archived baselines. Fresh JSON and logs are under `build/replay/`. The optional fresh PDF is `build/replayed-report.pdf`; baseline files remain unchanged. A locally rebuilt PDF need not be byte-identical because TeX embeds timestamps and identifiers, but it compiles from the pinned source.

## Contents

- `beta-renewal-asymptotics.tex` and `.pdf`: the integrated 14-page research article
- `proofs/central.md`: central derivation and inversion proof source
- `proofs/rare-tails.md`: separated-ratio rare-tail derivation source
- `scripts/central_polynomials.py`: cumulant-recurrence derivation of P1 through P4
- `scripts/derive_diagonal_fast.py`: diagonal coefficients through order 7
- `scripts/check_renewal.py`: exact simplex probabilities and diagonal counts
- `scripts/check_transition.py`: exact central-window diagnostics
- `scripts/check_rare_tail.py`: exact separated-ratio diagnostics
- `scripts/independent_central.py`: independent raw-moment logarithm construction, direct word-count dynamic programming, rectangular checks and inverse coefficients
- `scripts/independent_rare.py`: independent transform/saddle calculation and a different exact coefficient recurrence
- `scripts/validate_outputs.py`: failing assertions for displayed formulas, independent agreement and replay outputs
- `scripts/check_manifest.py`: SHA-256 payload verification
- `checks/`: reproducible JSON baselines and readable computation logs
- `SOURCES.md` and `source-hashes.json`: bibliography, provenance and bounded source-audit scope
- `VALIDATION.md`: concise verification summary
- `build.sh`, `replay.sh`, `requirements.txt`, `SHA256SUMS`: portable build and integrity files

The proof notes are supporting derivations; the integrated article is the authoritative statement of scope. In particular, the central note's final scope paragraph concerns that note alone; the separate rare-tail theorem is proved in the other note and integrated article. Script names in those notes refer to `scripts/` and generated results to `checks/`.

## Important limits

All orders and compact sets are fixed before taking the limit. No growing-order uniformity, effective universal numerical constants, uniform bridge between the central and fixed-ratio regimes, optimal truncation, or exponential-sector theorem is asserted. The rare-tail parameter is the exact integer ratio k/m. Smooth inverse carriers are explicitly chosen; exact integer thresholds require controlled brackets near rounding boundaries.

Finite computations check formulas, signs and indexing. The analytic arguments establish the remainder theorems. These are ordinary mathematical proofs and reproducible computations, not proof-assistant certificates.

No third-party full paper, unrelated repository source, private working report, or external credential is included. Bibliographic links and inspected-copy hashes are supplied instead.
