# Artifact map

- `report/report.pdf`, `report/report.tex`: paper and editable sources.
- `nine/generated/H2082_simple_positive.json`: cheapest nine-positive recommendation, 444 operations, degree 1,845,940.
- `nine/generated/H2057_refined_positive.json`: lowest-degree delivered nine-positive recommendation, 483 operations, degree 1,503,378.
- `nine/METRICS.json`: all twelve positive/nonnegative evaluator variants.
- `integer/generated/integer10.json`: ten unrestricted integers, 494 operations, degree 3,507,876.
- `integer/alternative_low_cost/generated/integer10.json`: ten unrestricted integers, 490 operations, degree 3,547,076.
- `algebra/p15_78_degree30.json`, `p15_87_degree26.json`, `p15_88_degree24.json`: short positive-variable forms with the separate complete 590069 coefficient tuple.
- `source/`, `carry/`: polynomial coordinate-change and packing certificates.
- `direct/stack_step_quartic.json`: local one-stack relation only, 91 total natural variables including two exposed states; not a consistency equation.
- `direct/OneStackEquation.lean`: uncompiled proposed global constructor; no final witness count is claimed.
- `*_audit/`: separately authored exact-data and mathematical reviews.
- `verify.py`, `negative_controls.py`: clean-copy replay and corruption controls.
- `PROVENANCE.json`, `SHA256SUMS.json`: retained-source and whole-deliverable identities.

Circuit JSONs use named intermediate nodes as abbreviations. Only their listed
inputs are quantified. Compressed fixed leaves represent actual integer
coefficients, not an extra parameter or oracle.
