# Divisor square partition asymptotics and inversion

Read `article/divisor-square-partitions.pdf`, a ten-page report on OEIS A301746, the coefficients of the product (1+q^k) raised to d(k)^2. Its editable LaTeX source is adjacent.

The report proves the posted logarithmic equivalent, gives three explicit forward and inverse corrections and a constructive hierarchy at every fixed logarithmic order. A separate arbitrary-order relative expansion keeps the saddle cumulants exact. It also proves global coefficient monotonicity and shrinking real-index brackets for the integer threshold inverse, including a first exact-cumulant inverse shift.

## Reproduce the checks

From the extracted package root, run:

    python3 verify.py

Python 3 with SymPy, mpmath, NumPy and SciPy is required. The dependency names are listed in `requirements.txt`. The independent checker uses only the Python standard library. The driver checks exact manifest coverage, all mathematical and visual approval links, then runs both producer programs and the independent checker in new temporary directories. It compares every saved receipt, cross-checks all displayed formal coefficients, rejects optimized Python, and verifies that no packaged file changed. No network access or numerical solver service is used.

To run an individual check, use a new output directory outside the package:

    python3 checks/producer/verify.py --output-dir /tmp/a301746-numeric-output
    python3 checks/producer/verify_log_series.py --output-dir /tmp/a301746-symbolic-output
    python3 audits/independent/check.py --output-dir /tmp/a301746-independent-output

Choose fresh directory names. The producer programs refuse to overwrite an existing receipt or write into their own source directory. Their default, if no output directory is given, is a newly created temporary directory. Do not use Python's `-O` mode.

## Rebuild the PDF separately

With a normal TeX Live installation, run from the package root:

    sh article/build.sh /tmp/a301746-pdf-build

Use a separate output directory, as in that command. The script's optional fallback handles a minimal Linux TeX installation, while normal TeX installations use their standard configuration. The source names its standard LaTeX packages. Rebuilding may change PDF metadata, so a newly built PDF need not have the frozen PDF's byte hash. The verifier is for the immutable delivered files, not the newly built output.

## Evidence and limits

`proofs/` contains immutable mathematical source snapshots. Historical wording such as “review pending” is superseded by `audits/independent/approval.json` and the integrated review. `audits/root-visual-approval.json` and `article/visual-qa.json` bind the final ten-page PDF and source.

The coefficient recurrences and formal reversion checks are exact. The high-precision saddle comparisons are numerical diagnostics, not interval-certified estimates. They corroborate the ordinary analytic proofs and are not proof premises. The supplied inverse error constants are asymptotic existence constants; they are not optimized numerical thresholds.

The report distinguishes expansions of the logarithm from relative coefficient expansions. It does not claim convergence of the formal hierarchies, an explicit complete exponential transseries, or a literature-wide first result. Possible deeper arithmetic contributions associated with zeta zeros are left open. No external publication or submission is asserted.

`SHA256SUMS` covers every other file. To retain that reproducibility record, leave the package unchanged and direct all generated outputs elsewhere.
