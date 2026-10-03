"""Independently evaluate the complete exported polynomial. Standard library only."""
from __future__ import annotations
import json
from pathlib import Path
import sys


def verify(path: Path) -> dict[str, int | str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("domain") != "nonnegative integers":
        raise ValueError("Unexpected coefficient-variable domain declaration")
    variables = data["variables"]
    if not all(isinstance(x, str) for x in variables) or len(variables) != len(set(variables)):
        raise ValueError("Variable names are malformed or repeated")
    if len(variables) != data["variable_count"]:
        raise ValueError("Declared variable count does not match")
    assignment = data["zero_assignment"]
    if set(assignment) != set(variables):
        raise ValueError("Assignment has missing or extra variables")
    if any(type(x) is not int or x < 0 for x in assignment.values()):
        raise ValueError("Assignment is outside the natural-number domain")
    seen = set()
    total = 0
    degree = 0
    for term in data["terms"]:
        monomial = tuple(term["monomial"])
        coefficient = term["coefficient"]
        if type(coefficient) is not int or coefficient == 0:
            raise ValueError("Invalid or unnecessarily zero coefficient")
        if monomial != tuple(sorted(monomial)) or monomial in seen:
            raise ValueError("Unnormalized or repeated monomial")
        if any(v not in assignment for v in monomial):
            raise ValueError("Undeclared variable occurs in polynomial")
        seen.add(monomial)
        degree = max(degree, len(monomial))
        value = coefficient
        for variable in monomial:
            value *= assignment[variable]
        total += value
    if len(seen) != data["monomial_count"]:
        raise ValueError("Monomial count discrepancy")
    if degree != data["degree"] or degree > 2:
        raise ValueError("Degree discrepancy or nonquadratic polynomial")
    if total != 0:
        raise ValueError(f"The supplied assignment is not a zero: value = {total}")
    return {"status": "PASS", "variables": len(variables), "degree": degree,
            "monomials": len(seen), "value": total}

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 verify_export.py PATH_TO_POLYNOMIAL_JSON")
    try:
        result = verify(Path(sys.argv[1]))
    except (OSError, ValueError, TypeError, KeyError) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
    print(json.dumps(result, indent=2))
