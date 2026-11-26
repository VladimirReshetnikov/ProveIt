# Beyond Dirichlet GRH: sharp torsion specialization

Prepared for Vladimir Reshetnikov, November 25, 2026.

## Main deliverable

Read grh_fixed_field_transfer.pdf. Its editable source is
 grh_fixed_field_transfer.tex plus sections/*.tex and data/bound_comparison.tex.

The report proves two local results inspired by the simultaneous twisting
argument in lsernau/grh-lean:

1. The exact zero-tolerance obstruction cost over any fixed finite extension
   K/Q_p is sum_h p^(-min(v_p(e_K),h-1)). It is attained by explicit binomials.
2. In d variables, every individual Gauss-valuation constraint can be preserved
   at one torsion tuple with order exponents at most
   h0 + ceil((3^(d-1)-1) log_p(1+B/rho)) + floor(p^v_p(e_K) B).
   This removes the previous iterated coefficient-field-extension bound.

Both extend to integral formal power series. The report also explains the
near-full-rank requirement of the source determinant argument and why the new
local results do not by themselves resolve a further global conjecture.

These are complete paper proofs with independent review and exact finite
checks. They are not presented as new Lean-verified theorems. Historical
bibliographic priority has not been established.

## Reproduce

With Python 3:

    python3 code/torsion_bounds.py --p 2 --e 1 --dimension 3 --rho 1 --budget 3
    python3 code/check_zero_tolerance.py --output checks/reproduced_zero_tolerance.json
    python3 code/finite_slope_checks.py

The bound calculator and slope checks use the standard library. The scalar
verification script additionally needs SymPy; install the recorded version with
`python3 -m pip install -r requirements.txt`. The slope check writes code/finite_slope_checks.json. The recorded
reference result is checks/finite_slope_checks.json.

To compile the manuscript with a complete TeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error grh_fixed_field_transfer.tex
    pdflatex -interaction=nonstopmode -halt-on-error grh_fixed_field_transfer.tex

## Contents

- sections/: complete mathematical proofs, source analysis, prior-work catalog,
  and references.
- code/: a usable exact bound calculator and independent verification scripts.
- checks/: recorded finite-check certificates, summaries, and validation logs.
- audit/: pinned source hashes, a 31-archive comparison matrix, extraction
  manifest, and independent mathematical review notes.
- data/: exact cutoff comparisons.
- results.json: compact status and theorem ledger.
- SHA256SUMS.txt: hashes for the final package files, excluding the manifest itself.

The prior-work matrix records what those earlier reports claim. It does not
independently recertify every earlier proof or computation. The authoritative
new statements are the theorems in the PDF. Supporting audit notes can also
mention intermediate weaker bounds established during the derivation.

Upstream: 72fead102f663d5c7a407964a13dc0cf9d977207.
ProveIt incoming snapshot: 274841c1cb137aafbb60ab5f519c51fd42eee98e.
No remote repository was modified.
