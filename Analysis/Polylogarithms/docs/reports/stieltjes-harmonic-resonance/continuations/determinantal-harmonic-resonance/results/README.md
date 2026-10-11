# Recorded results

- `exact_checks.json`: 732 finite exact assertions, categorized by purpose.
- `exact_formulas.json`: exact rank 1–4 cutoff and primitive formulas.
- `numerical_checks.json`: 85 floating-point diagnostics, working precision
  100 digits, with each tolerance and observed discrepancy. These are not
  interval-certified results.
- `build_review.json`: final compilation and PDF-review record.

In formula expressions `Lk` denotes Li_k(z), `Dk` denotes Li_{k,1}(z,1),
`N` denotes the maximum index, and `u` denotes the spectral parameter.
The key `generating_functions[q]` represents Theta^{-q} G_r(z), with
Theta = z d/dz. Endpoint values for q >= 1 are ordinary convergent sums.

The verification scripts rewrite the first three JSON files. Run them
on a copy when preserving delivered records. Compilation or visual
review is not rerun by those scripts; a changed PDF needs a fresh
review record.
