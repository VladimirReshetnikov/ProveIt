#!/usr/bin/env python3
"""Independent symbolic leading-part and scalar cross-check of four Pell DAGs.

This is a finite algebra audit, not a proof of the unbounded Pell lemmas.
It uses a separate scalar implementation and sparse leading polynomials.
"""
from __future__ import annotations
import hashlib
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "pell_work"
NAMES = ["J", "F", "alpha", "i", "T", "w", "s", "n", "eta", "zeta",
         "beta", "K0", "MC", "MF"]
POS = {name: j for j, name in enumerate(NAMES)}
ZERO = (0,) * len(NAMES)


def add(a, b, sign=1):
    out = dict(a)
    for mon, coeff in b.items():
        out[mon] = out.get(mon, 0) + sign * coeff
        if not out[mon]:
            del out[mon]
    return out


def mul(a, b):
    out = {}
    for am, ac in a.items():
        for bm, bc in b.items():
            mon = tuple(x + y for x, y in zip(am, bm))
            out[mon] = out.get(mon, 0) + ac * bc
    return {m: c for m, c in out.items() if c}


def power(a, n):
    out = {ZERO: 1}
    while n:
        if n & 1:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def symbol(name):
    mon = list(ZERO)
    mon[POS[name]] = 1
    return {tuple(mon): 1}


def degree(a):
    return max(sum(mon[:10]) for mon in a) if a else -1


def leading_audit(graph, den, weight):
    leading = {name: symbol(name) for name in NAMES}
    degrees = {name: int(j < 10) for j, name in enumerate(NAMES)}
    def atom(a):
        if isinstance(a, int):
            return {ZERO: a} if a else {}, 0 if a else -1
        return leading[a], degrees[a]
    for name, op, av, bv in graph["source"]:
        a, da = atom(av)
        b, db = atom(bv)
        if op == "*":
            p = mul(a, b)
        elif da > db:
            p = a
        elif db > da:
            p = b if op == "+" else {m: -c for m, c in b.items()}
        else:
            p = add(a, b, 1 if op == "+" else -1)
            if not p:
                raise ValueError(f"Complete leading cancellation at {name}; this auditor needs a lower-part calculation")
        leading[name], degrees[name] = p, degree(p)
    q0 = mul(symbol("beta"), symbol("J"))
    k0 = add(symbol("eta"), symbol("zeta"))
    c0 = add(add(q0, symbol("F"), -1), symbol("alpha"), -1)
    if weight == "V2":
        exponents = {"i": 20, "w": 48 if den == "XY" else 46,
                     "s": 110 if den == "XY" else 108, "T": 4}
        expected = {ZERO: 2**14}
        expected = mul(expected, power(q0, 378))
        expected = mul(expected, power(k0, 64))
        expected = mul(expected, power(c0, 2))
    else:
        exponents = {"i": 14, "w": 36 if den == "XY" else 34,
                     "s": 82 if den == "XY" else 80, "T": 2}
        expected = {ZERO: -(2**10)}
        expected = mul(expected, power(q0, 284))
        expected = mul(expected, power(k0, 46))
    for name, exponent in exponents.items():
        expected = mul(expected, power(symbol(name), exponent))
    output = graph.get("output", graph["source"][-1][0])
    if leading[output] != expected:
        raise ValueError(f"Leading homogeneous polynomial mismatch: {den}/{weight}")
    if degrees[output] != graph["exact_degree"]:
        raise ValueError("Recorded degree mismatch")
    return degrees[output], len(expected)


def scalar_formula(v, den, weight, mod):
    # Independent formulas, deliberately not the source gate schedule.
    J, F, alpha, i, T, w, s, n, eta, zeta = [v[k] for k in NAMES[:10]]
    beta, K0, MC, MF = [v[k] for k in NAMES[10:]]
    q = (beta * J + 1) % mod
    h = (q - 1) % mod
    C = (q - F - alpha) % mod
    X = w * q % mod
    Y = pow(q, 3, mod) * s % mod
    k = (eta + zeta) % mod
    c = (k * Y + eta) % mod
    A = (Y * (X + 1) + 1) % mod
    Delta = (A*A - 1) % mod
    H = (4*A - 5) % mod
    D = X*Y % mod if den == "XY" else pow(q, 4, mod)
    V0 = X * Y * Y % mod
    E = (1 + V0 * (V0 + 1) * k * k) % mod
    R = ((h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J) % mod
    e = (k-R-1) % mod
    B = ((K0+w)*C-F) % mod
    U = i*c*c % mod
    a = Delta*U*U*E % mod
    G = E*(1+a) % mod
    Fsq = pow(1+2*a, 2, mod)
    Q = Delta*(Fsq-1) % mod
    b = (c*T-R) % mod
    V = (Fsq*b-c) % mod
    L = V*V % mod if weight == "V2" else b*V % mod
    Kpos = (X*(3*c-2*X)+2) % mod
    M = h*D*H % mod
    Z = (h*D*(H*(n-L*B)+Kpos)-H*(D*B+h*e)) % mod
    return ((Q-1)*Z*Z-M*M*G*(Q*V*V-1)) % mod


def dag_eval(graph, values, mod):
    d = dict(values)
    def atom(x):
        return x if isinstance(x, int) else d[x]
    for name, op, a, b in graph["source"]:
        x, y = atom(a), atom(b)
        d[name] = (x+y if op == "+" else x-y if op == "-" else x*y) % mod
    return d[graph.get("output", graph["source"][-1][0])]


def main():
    rng = random.Random(20261025)
    receipts = []
    for den in ("XY", "q4"):
        for weight in ("V2", "bV"):
            filename = f"equation_{den}_{weight}.json"
            path = ROOT / filename
            graph = json.loads(path.read_text())
            known = set(NAMES)
            dependencies = {}
            for name, op, a, b in graph["source"]:
                if name in known or op not in ("+", "-", "*"):
                    raise ValueError("Bad DAG declaration")
                parents = {x for x in (a, b) if isinstance(x, str)}
                if not parents <= known:
                    raise ValueError("Forward or undeclared operand")
                known.add(name)
                dependencies[name] = parents
            output = graph.get("output", graph["source"][-1][0])
            live, stack = set(), [output]
            while stack:
                node = stack.pop()
                if node in live:
                    continue
                live.add(node)
                stack.extend(dependencies.get(node, ()))
            if live != known:
                raise ValueError("Unused gate or input")
            deg, leading_terms = leading_audit(graph, den, weight)
            for _ in range(120):
                # All signs sampled to check identities independently of domain.
                values = {k: rng.randrange(-1000, 1001) for k in NAMES}
                prime = (2**127-1) if _ % 2 else (2**61-1)
                if dag_eval(graph, values, prime) != scalar_formula(values, den, weight, prime):
                    raise ValueError("Independent scalar formula mismatch")
            receipts.append({"file": filename, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                             "operations": len(graph["source"]), "exact_degree": deg,
                             "leading_terms": leading_terms, "modular_scalar_checks": 120,
                             "all_nodes_inputs_ports_live": True})
    print(json.dumps({"status": "passed", "checks": receipts,
                      "scope": "Exact leading-part identity and DAG liveness; scalar random checks are regression checks only."}, indent=2))


if __name__ == "__main__":
    main()
