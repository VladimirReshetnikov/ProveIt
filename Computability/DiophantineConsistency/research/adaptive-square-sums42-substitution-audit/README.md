# Direct substitution scan for the 42-variable quartic

`audit.py` pins the exact 42-variable graph and expands its 33 squared
residuals as sparse integer polynomials. It tests each of the 29 positive
named coordinates with a direct defining equality by substituting the
recorded expression and removing only that coordinate's defining residual.

Every tested substitution leaves another residual with a monomial of degree
at least three. Its nonzero coefficient is an integer times a power of beta,
which is nonzero for the fixed positive beta. The captured output and hashes
are in [the audit receipt](../../reviews/adaptive-square-sums42-substitution-audit/receipt.json).
Run `python3 Computability/DiophantineConsistency/research/adaptive-square-sums42-substitution-audit/audit.py`
from the repository root to reproduce it.

This finite audit concerns only one-coordinate direct substitution in this
particular sum-of-squares presentation. It does not rule out joint changes,
replacing residuals, other algebraic rewrites, or a smaller quartic. It is not
a Lean theorem or a global minimality result.
