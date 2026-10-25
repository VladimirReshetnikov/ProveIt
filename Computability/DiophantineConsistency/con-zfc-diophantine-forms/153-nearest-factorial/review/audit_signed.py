#!/usr/bin/env python3
"""Reviewer checks: no imports from the producer or its checker.

The finite scope is topology, modified formula cuts, an exact norm identity,
and the complete scalar cancellation polynomials. Semantic scope is stated
separately in signed_mathematics_review.md.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMPONENT = None


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


class Polynomial:
    """Ordinary sparse integer polynomials, a reviewer-local implementation."""

    def __init__(self, dimension, terms):
        self.dimension = dimension
        self.terms = {tuple(m): int(c) for m, c in terms.items() if c}

    @classmethod
    def constant(cls, dimension, value):
        return cls(dimension, {(0,) * dimension: value})

    @classmethod
    def variable(cls, dimension, index):
        powers = [0] * dimension
        powers[index] = 1
        return cls(dimension, {tuple(powers): 1})

    def coerce(self, value):
        if isinstance(value, Polynomial):
            require(value.dimension == self.dimension, "mixed polynomial rings")
            return value
        require(type(value) is int, "noninteger scalar")
        return self.constant(self.dimension, value)

    def __add__(self, value):
        value = self.coerce(value)
        terms = dict(self.terms)
        for powers, coefficient in value.terms.items():
            terms[powers] = terms.get(powers, 0) + coefficient
        return Polynomial(self.dimension, terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial(self.dimension, {m: -c for m, c in self.terms.items()})

    def __sub__(self, value):
        return self + (-self.coerce(value))

    def __rsub__(self, value):
        return self.coerce(value) - self

    def __mul__(self, value):
        value = self.coerce(value)
        terms = {}
        for left, a in self.terms.items():
            for right, b in value.terms.items():
                powers = tuple(x + y for x, y in zip(left, right))
                terms[powers] = terms.get(powers, 0) + a * b
        return Polynomial(self.dimension, terms)

    __rmul__ = __mul__

    def __pow__(self, power):
        require(type(power) is int and power >= 0, "invalid polynomial power")
        result = self.constant(self.dimension, 1)
        base = self
        while power:
            if power & 1:
                result = result * base
            power >>= 1
            if power:
                base = base * base
        return result


def ring(names):
    return [Polynomial.variable(len(names), i) for i in range(len(names))]


def exact_equal(left, right, label):
    require(not (left - right).terms, "exact identity failed: " + label)


def local_dag_value(dag, register, atom_names):
    named = dict(dag["named_registers"])
    named.update({node[1]: i for i, node in enumerate(dag["nodes"])
                  if node[0] in ("variable", "coefficient")})
    atoms = ring(atom_names)
    memo = {named[name]: atom for name, atom in zip(atom_names, atoms)}

    def visit(i):
        if i not in memo:
            node = dag["nodes"][i]
            if node[0] == "integer":
                memo[i] = Polynomial.constant(len(atoms), node[1])
            else:
                require(node[0] in ("add", "sub", "mul"), "unexpected cut leaf")
                left, right = visit(node[1]), visit(node[2])
                memo[i] = (left + right if node[0] == "add" else
                           left - right if node[0] == "sub" else left * right)
        return memo[i]

    return visit(named[register]), atoms


def audit_dag(name, expected_variables, expected_operations):
    path = COMPONENT / (name + ".json")
    raw = path.read_bytes()
    dag = json.loads(raw)
    nodes = dag["nodes"]
    require(len(set(dag["variables"])) == expected_variables, "variable count")
    require(dag["variable_count"] == expected_variables, "declared variable count")
    degrees = []
    for i, node in enumerate(nodes):
        tag = node[0]
        if tag in ("add", "sub", "mul"):
            require(len(node) == 3 and all(type(j) is int and 0 <= j < i
                                          for j in node[1:]), "not a DAG")
            left, right = (degrees[j] for j in node[1:])
            degrees.append(left + right if tag == "mul" else max(left, right))
        else:
            require(tag in ("integer", "variable", "coefficient"), "unknown gate")
            degrees.append(1 if tag == "variable" else 0)
    live, pending = set(), [dag["output"]]
    while pending:
        i = pending.pop()
        if i not in live:
            live.add(i)
            if nodes[i][0] in ("add", "sub", "mul"):
                pending.extend(nodes[i][1:])
    require(len(live) == len(nodes), "dead nodes")
    actual_variables = [node[1] for node in nodes if node[0] == "variable"]
    require(Counter(actual_variables) == Counter(dag["variables"]), "variable leaves")
    counts = Counter(node[0] for node in nodes if node[0] in ("add", "sub", "mul"))
    require(sum(counts.values()) == expected_operations, "operation count")
    require(dict(counts) == dag["operation_counts"], "operation metadata")
    ports = sorted(node[1] for node in nodes if node[0] == "coefficient")
    require(ports == sorted(["beta", "K0", "MC", "MF", "cone_A", "cone_B"]),
            "fixed numeral leaves")

    ell, (X, Y) = local_dag_value(dag, "ell", ["X", "Y"])
    exact_equal(ell, X * Y**2, "ell=XY^2")
    k, (R, h, ell) = local_dag_value(dag, "k", ["R", "h", "ell"])
    exact_equal(k, R + 1 + h * ell, "k=R+1+h ell")
    budget_name = "Budget" if name == "integer11_degree298" else "budget"
    budget, (Y, k, q, error, eta) = local_dag_value(
        dag, budget_name, ["Y", "k", "q", "Derr", "eta"])
    exact_equal(budget, Y**2 * (k**2 * (q**2 - error) - 4*q**2*eta**2)
                - k**2*q**6, "Budget6")
    return {"name": name, "sha256": hashlib.sha256(raw).hexdigest(),
            "variables": expected_variables, "nodes": len(nodes),
            "live_operations": dict(counts), "operation_count": expected_operations,
            "syntactic_degree_bound": degrees[dag["output"]],
            "exact_modified_formula_cuts": ["ell", "k", "Budget6"]}


def primitive_norm_identity():
    b, d, e, s = ring(["b", "d", "e", "s"])
    G = 4*b + 1
    K = d*(s*(s+1)-b)-e
    N = K*K-G*d*e
    x = 2*s+1
    exact_equal(16*N, (d*(x*x+G)-4*e)**2-4*d*d*x*x*G,
                "primitive odd-carrier identity")


def scalar_center():
    names = ["A", "c", "r", "T", "R"]
    A, c, r, T, R = ring(names)
    delta0 = A*A-1
    Dm = 1+delta0*c*c
    B = r*A*Dm
    U = r*c*c*Dm
    Df = 1+delta0*c**4*B
    Q = delta0**2*c**4*B
    V = Df*(c-R+4*A*U*T)-c
    Psi = ((32*delta0+16)*U-4*r*c**4)*V \
          + U**2*T*(8*U*(c*c-2)+64*A**3+r*c**4*(3*c*c-16))
    before_aux = Psi**2-1024*B*Df*V**2
    after_aux = (Q-1)*before_aux-1024*B*Df*(V**2-1)
    exact_equal(after_aux, (Q-1)*Psi**2-1024*B*Df*(Q*V**2-1),
                "scalar cancellation cut")
    weights = [3, 1, 1, 1, 5]

    def weighted(poly):
        degree = max(sum(a*b for a, b in zip(m, weights)) for m in poly.terms)
        top = {m: c for m, c in poly.terms.items()
               if sum(a*b for a, b in zip(m, weights)) == degree}
        return degree, top

    ddegree, dtop = weighted(before_aux)
    edegree, etop = weighted(after_aux)
    require(ddegree == 80 and edegree == 108, "center degrees")
    expected_d = 512*A**15*c**24*r**5*T*R + 8192*A**17*c**22*r**5*T**2 \
                 - 4096*A**16*c**24*r**6*T**2
    expected_e = 512*A**22*c**30*r**6*T*R - 8192*A**24*c**28*r**6*T**2 \
                 - 4096*A**23*c**30*r**7*T**2
    require(dtop == expected_d.terms and etop == expected_e.terms,
            "entire weighted leading forms")
    saved = json.loads((COMPONENT / "center_remainder.json").read_text())
    for label, polynomial in [("Dcenter", before_aux), ("Ecenter", after_aux)]:
        exact_saved = {tuple(m): c for m, c in saved[label]}
        require(exact_saved == polynomial.terms, "saved coefficients: " + label)
    return {"variables": names, "weights": weights,
            "pre_auxiliary_degree": ddegree, "post_auxiliary_degree": edegree,
            "pre_auxiliary_terms": len(before_aux.terms),
            "post_auxiliary_terms": len(after_aux.terms),
            "all_saved_coefficients_match": True,
            "leading_forms_match": True}


def main():
    global COMPONENT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--component", type=Path,
                        help="Directory holding the four reviewed equation DAGs")
    parser.add_argument("--receipt", type=Path,
                        help="Write the compact JSON receipt here; otherwise read-only")
    args = parser.parse_args()
    candidates = ([args.component] if args.component else
                  [HERE.parent / "signed", HERE])
    COMPONENT = next((path for path in candidates
                      if (path / "integer14_degree82.json").is_file()), None)
    require(COMPONENT is not None, "component not found; supply --component")
    equations = [audit_dag("integer14_degree82", 14, 113),
                 audit_dag("integer14_degree90", 14, 111),
                 audit_dag("integer13_degree152", 13, 126),
                 audit_dag("integer11_degree298", 11, 150)]
    primitive_norm_identity()
    result = {"status": "PASS", "equations": equations,
              "primitive_odd_norm_identity": True, "scalar_center": scalar_center(),
              "scope": "Finite algebra and syntax only; see signed_mathematics_review.md for semantic review."}
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
