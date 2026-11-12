# Unselected support-derived-rank experiment

This source preserves the implementation-size experiment in Section 9 of the paper. It is not the delivered proof checker, is not covered by the accepted/rejected certificate test counts, and is not used in the main correctness theorem.

`python3 measure.py` from the package root reproduces its size separately under `unselected_experiments` in `evidence/metrics.json`. The mathematical quotient argument is in `reference/optional_support_quotient.tex`. The selected checker is `code/packet/checker.py`.
