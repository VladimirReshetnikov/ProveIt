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

`audit_pairs.py` additionally tests all 406 pairs of these substitutions,
including their dependency order, and checks that both removed defining
residuals vanish. Every pair leaves a residual with a nonzero pure-beta
monomial of degree at least three. Its complete [per-pair output and receipt](../../reviews/adaptive-square-sums42-substitution-audit/pairs-receipt.json)
are saved separately.

These finite audits concern one or two direct substitutions in this particular
sum-of-squares presentation. They do not rule out three or more simultaneous
changes, replacing residuals, other algebraic rewrites, or a smaller quartic.
They are not Lean theorems or global minimality results.
