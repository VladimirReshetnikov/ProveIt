# Data

`oeis_prefix.json` contains precisely the first 58 terms displayed on the live A239950 page inspected on 2026-10-04, with offset zero. It is a finite external cross-check, not a downloaded b-file. The build computes its own `generated/exact_terms.txt` for n=0,...,1500.

Generated receipts belong to the release's `generated/` directory and are regenerated during every build. They are never used as authoritative input to the mandatory exact calculation.
