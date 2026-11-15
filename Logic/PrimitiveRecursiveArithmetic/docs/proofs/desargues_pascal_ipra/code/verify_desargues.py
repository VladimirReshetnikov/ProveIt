#!/usr/bin/env python3
"""Exact universal Desargues and 3x3 adjugate polynomial certificates.

Uses the standard-library sparse polynomial implementation in verify_pascal.py.
The two scripts may be placed together; the development ../pascal location is
also supported. Coefficients are integers, and monomials are canonical sorted
variable-index tuples. No random or numerical sampling is used here.

Run: python3 verify_desargues.py
"""
from pathlib import Path
import json
import sys

script_dir = Path(__file__).resolve().parent
for candidate in (script_dir, script_dir.parent / "pascal"):
    if (candidate / "verify_pascal.py").is_file():
        sys.path.insert(0, str(candidate))
        break
else:
    raise SystemExit("Place verify_pascal.py alongside verify_desargues.py")

from verify_pascal import add, check, cross, det3_columns, mul, var


def dot(u, v):
    return add(*(mul(a, b) for a, b in zip(u, v)))


def main():
    points = [[var(3 * i + j) for j in range(3)] for i in range(6)]
    a, b, c, A, B, C = points
    X = cross(cross(a, b), cross(A, B))
    Y = cross(cross(b, c), cross(B, C))
    Z = cross(cross(c, a), cross(C, A))
    joins = (cross(a, A), cross(b, B), cross(c, C))
    lhs = det3_columns(X, Y, Z)
    rhs = mul(det3_columns(a, b, c), det3_columns(A, B, C),
              det3_columns(*joins))
    certificates = [check(
        "Desargues: det of side meets equals product of triangle and join determinants",
        lhs, rhs)]

    # Independent line and center variables.  This verifies the generic
    # incidence-to-determinant identity, not merely its Desargues substitution.
    l1, l2, l3, o = [[var(3 * i + j) for j in range(3)] for i in range(4)]
    determinants = det3_columns(l1, l2, l3)
    cofactor_columns = (cross(l2, l3), cross(l3, l1), cross(l1, l2))
    incidences = (dot(o, l1), dot(o, l2), dot(o, l3))
    for component in range(3):
        certificates.append(check(
            "Incidence-to-determinant adjugate certificate, component %d" % component,
            mul(determinants, o[component]),
            add(*(mul(incidences[i], cofactor_columns[i][component])
                  for i in range(3)))))

    print(json.dumps({
        "description": "Exact universal polynomial identities over Z",
        "desargues_coordinate_variables": 18,
        "desargues_degree": 12,
        "desargues_monomial_count": len(lhs),
        "desargues_coefficients": sorted(set(lhs.values())),
        "adjugate_coordinate_variables": 12,
        "adjugate_component_degree": 4,
        "certificates": certificates,
        "status": "all identities verified",
        "limitation": "This exact polynomial checker is not a compiled iPRA or Lean proof object."
    }, indent=2))


if __name__ == "__main__":
    main()
