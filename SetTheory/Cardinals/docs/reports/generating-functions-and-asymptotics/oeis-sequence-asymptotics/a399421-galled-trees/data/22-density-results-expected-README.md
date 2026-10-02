# Frozen numerical references

These are the preserved original integer and numerical outputs, separate from fresh replay outputs. They are regression references, not numerical certificates.

- `independent-rows.json`: exact bivariate rows through 160; finite-size statistics use binary floating point
- `constants.json`, `numerics.txt`: cutoff 160, 80 decimal working digits
- `density-checks.json`, `density-numerics.txt`: 55 decimal working digits
- `stability/cutoff120-dps80.json`: cutoff 120, 80 decimal working digits
- `stability/cutoff160-dps60.json`: cutoff 160, 60 decimal working digits
- `amplitude-check.json`: independent scalar calculation, 85 decimal working digits
- `triangle-verification.json`: public numeric-reference row/cell count
- `stability-summary.json`: absolute differences calculated from the frozen constant outputs

Public numeric OEIS input is in `data/oeis-reference.json`, relative to the report root. The public-source comparison is limited to those supplied initial terms; all later rows are independently generated.
