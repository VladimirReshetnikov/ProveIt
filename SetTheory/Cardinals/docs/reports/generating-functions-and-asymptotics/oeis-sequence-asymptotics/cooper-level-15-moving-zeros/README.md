# Modular connection constants and a two-root asymptotic transition

This package contains the article, editable LaTeX, an offline PDF build script, exact coefficient data, and a self-contained mathematical replay.

## Results

The article gives explicit path and connection proofs for all ten constants in Cooper's Table8, a generator for every fixed correction order, and a qualified inverse for positive sequences. Its principal parameter-uniform result concerns Cooper's level15 family near epsilon=-5:

T_{-5+u/n}(n)/(A 6^n n^(-3/2))
= exp(u/6)+10(-1)^n exp(-u/6)+O(1/n),

where A=6^(3/2)/(20 pi^(3/2)). The error is additive and uniform for bounded complex u, and the article constructs every fixed order. For odd n there is exactly one local real parameter zero near

epsilon_n=-5+3 log(10)/n+[162/125-(9/2)log(10)]/n².

The article proves the localization and further terms. It does not claim global uniqueness of polynomial zeros or a relative equivalent at the cancellation point.

## Attribution and limits

The ten constant formulas are earlier formulas, not new conjectured values. A284756 already records the level11 equivalent due to Vaclav Kotesovec (2017). Cooper (2024) supplies the parameter families and Table8. Guillera--Zudilin (2013) supplies the earlier positive modular radial principle; Cooper--Ye (2016) supplies relevant negative-axis modular machinery. The article's references give direct source links. The literature comparison is bounded and does not establish historical priority.

The inverse statement keeps an unknown asymptotic error inside the integer ceiling. It is not a certified finite-n enclosure with a computable error constant. The replay's inverse examples verify specific integer thresholds directly from exact neighboring recurrence values.

## Exact-data conventions

In expected_coefficients.json, the symbol x in a primary fixed-case coefficient denotes the selected algebraic root r=1/R. The auxiliary coefficients are already evaluated in their algebraic fields. In the crossover data, e denotes epsilon, u is the competition variable, and U is a limiting zero. The article defines the relevant branches.

## Run the mathematical replay

Requires Python3.10 or newer, SymPy1.14.0 and mpmath1.3.0. Install those standard dependencies with:

    python -m pip install -r requirements.txt

No network access is used by the replay itself:

    python verify_manifest.py
    python replay.py --output replay_results.json

The replay normally finishes in roughly ten seconds. It asserts:

- Exact b0 through b6 for all ten fixed cases, and exact amplitude polynomial identities
- Exact matrix and eta-multiplier calculations for the difficult negative connections
- High-precision eta identities and fixed-point derivatives at the stated sample points
- Finite recurrence/asymptotic comparisons through n=2000 for all ten cases
- Exact crossover polynomials and zero coefficients through order3, plus the Appell derivative identity through degree12
- Additive sample checks for both parities and complex u, including the cancellation value
- Moving odd-index zeros and one fixed complex zero branch of each parity from the quartic recurrence, with residual checks
- Inverse examples checked against exact integer recurrence neighbors

These are finite computational checks. They neither prove the analytic remainders from samples nor replace the article's proofs. Numeric calculations use100 decimal digits and are not interval-arithmetic certificates. The saved expected_replay.json records one passing run; low-level roundoff displays can vary with dependency versions.

## Rebuild the article

With a standard TeX installation containing the packages named in the LaTeX preamble:

    bash build.sh

The script uses only local files and fixes PDF metadata for reproducibility. The editable source is included. The manifest authenticates the sealed source, article, code and reference output. Newly generated replay output need not be listed in the manifest.

Nothing in this package performs a public edit, submission, upload, or network request.
