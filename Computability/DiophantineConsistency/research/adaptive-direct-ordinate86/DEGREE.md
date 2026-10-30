# Exact degree certificate for the displayed 86-operation polynomial

[`verify_degree86.py`](verify_degree86.py) uses the separately checked sparse integer-polynomial expansion of the four displayed factors, treating the thirteen unknowns as variables and the four fixed ports as symbolic coefficients. It checks exact upper bounds on the total degree in the unknowns and prints a top-degree monomial of each factor whose coefficient is a single nonzero power of the fixed `beta`, with no dependence on the other ports:

| Factor | Degree | Witness monomial | Coefficient |
|---|---:|---|---:|
| first | 15 | `J^9 X^2 Y^2 eta^2` | `-2 beta^9` |
| main | 13 | `J^4 X^2 Y^5 eta gamma` | `8 beta^4` |
| auxiliary | 18 | `J^8 f^6 X^2 Y^2` | `beta^8` |
| strong | 10 | `i^2 Y^4 eta^4` | `1` |

The JSON name `i` is printed as the distinct unknown `g` in `equation86.pdf`. The printed constant `beta=(2^47)^2011-1` is positive. Therefore each displayed top coefficient remains nonzero after fixing all four ports, so these are exact factor degrees. The product of nonzero leading homogeneous polynomials over the integers is nonzero; hence the product minus one has exact degree `15+13+18+10=56`. Replacing each natural variable by itself plus one preserves the leading homogeneous part, so the positive-shifted polynomial has the same degree.

This is a reproducible exact integer-polynomial certificate and a mathematical argument, not a Lean proof of the degree and not a minimality claim. Run `python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_degree86.py` from the repository root; its saved output is [`verify_degree86.out`](verify_degree86.out). The checker depends on `verify_equation86.py`, which also checks the pinned equation display and JSON. The PDF intentionally omits the degree pending independent review.
