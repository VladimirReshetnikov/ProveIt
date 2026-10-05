# Optional numerical diagnostics

`saved_dp_3000.json` contains a prior exact-integer recurrence computation through n=3000, evaluated with mpmath at 75 decimal digits afterward. It is a numerical consistency experiment, not an interval enclosure or proof of amplitude digits.

Reproduce from the package root using `python3 diagnostics/reproduce_dp.py 3000 fresh_dp_3000.json`. Install mpmath 1.3.0 and SymPy 1.14.0 first if needed. The output file is relative to this directory; existing output files are rejected. `endpoint_9.json` is an identical copy of the independently checked coefficient table in `checks/inputs/`.

Normal and `python -O` runs at n=100 are included and agree exactly in their printed 55-digit correction values with the n=100 row of the saved n=3000 experiment. No high-cost full dynamic program is part of the exact algebra suite. To assess numerical rather than exact symbolic agreement, the reader may independently increase the range or working precision; that still does not certify the unknown asymptotic remainder.
