# Direct substitution scan for the 47-variable quartic

Run `python3 Computability/DiophantineConsistency/research/adaptive-square-sums47-substitution-audit/audit.py` from the repository root. The script pins the exact 47-variable candidate and expands its 33 residuals as sparse integer polynomials. For each of the 24 positive named coordinates with a directly recorded equality to a coordinate-free expression, it substitutes that defining expression and removes only that coordinate's own equality residual.

Every tested substitution leaves another residual with a monomial of degree at least three. The printed witness has coefficient `c*beta^k` with nonzero integer `c`, so it remains nonzero for the actual fixed `beta = (2^47)^2011 - 1`. Thus this particular direct-substitution strategy cannot retain all residuals at degree at most two; the resulting unchanged sum-of-squares presentation has degree above four. The result is a finite computation, not a Lean theorem. It does not rule out simultaneous substitutions, replacement of residuals, exploiting constraints, other rewrites, or a smaller quartic.

The captured output and hashes are in [the audit receipt](../../reviews/adaptive-square-sums47-substitution-audit/receipt.json).
