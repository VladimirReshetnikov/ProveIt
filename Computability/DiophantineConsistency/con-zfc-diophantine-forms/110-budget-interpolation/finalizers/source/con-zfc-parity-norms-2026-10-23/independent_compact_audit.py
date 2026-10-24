#!/usr/bin/env python3
"""Independent exact audit of compact norms and their literal DAGs.

This file never imports a builder. Generic norm identities are checked in
the integer polynomial ring by successive conjugation in a formal
multiquadratic algebra. The supplied compact DAG is then evaluated in that
same polynomial ring and compared coefficient for coefficient. Literal
Diophantine DAGs are checked for syntax, liveness, operation counts, exact
degree, and agreement with their independently parsed source packets.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import time

from independent_graph_audit import Line, expression, evaluate_packet, load_coefficients, require


class Polynomial:
    """Sparse integer polynomials; six exponents packed in radix 64.

    All identities below have individual degrees at most 32, so addition
    of exponent encodings cannot carry between exponent slots.
    """
    width = 6
    dimension = 6

    def __init__(self, value=0):
        self.terms = ({k: v for k, v in value.items() if v}
                      if isinstance(value, dict) else ({0: value} if value else {}))

    @classmethod
    def variable(cls, index):
        return cls({1 << (cls.width * index): 1})

    @classmethod
    def coerce(cls, value):
        return value if isinstance(value, cls) else cls(value)

    def __add__(self, value):
        value = self.coerce(value)
        out = self.terms.copy()
        for k, v in value.terms.items():
            out[k] = out.get(k, 0) + v
        return Polynomial(out)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({k: -v for k, v in self.terms.items()})

    def __sub__(self, value):
        return self + -self.coerce(value)

    def __rsub__(self, value):
        return self.coerce(value) - self

    def __mul__(self, value):
        value = self.coerce(value)
        out = {}
        for k, v in self.terms.items():
            for l, w in value.terms.items():
                out[k + l] = out.get(k + l, 0) + v * w
        return Polynomial(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, "fixed nonnegative exponent")
        out, base = Polynomial(1), self
        while n:
            if n & 1:
                out = out * base
            n >>= 1
            if n:
                base = base * base
        return out

    def __eq__(self, value):
        return self.terms == self.coerce(value).terms

    def digest(self):
        expanded = [[[(k >> (self.width * j)) & 63 for j in range(self.dimension)], v]
                    for k, v in sorted(self.terms.items())]
        return hashlib.sha256(json.dumps(expanded, separators=(",", ":")).encode()).hexdigest()


def formal_norm(x, radicands):
    """Multiply conjugates without a pre-expanded norm formula."""
    value = {0: x, **{1 << j: Polynomial(-1) for j in range(len(radicands))}}
    trace = []
    for j in range(len(radicands)):
        conjugate = {m: -v if m & (1 << j) else v for m, v in value.items()}
        output = {}
        for a, u in value.items():
            for b, v in conjugate.items():
                scalar = u * v
                common = a & b
                for k, d in enumerate(radicands):
                    if common & (1 << k):
                        scalar = scalar * d
                target = a ^ b
                output[target] = output.get(target, Polynomial(0)) + scalar
        value = {m: p for m, p in output.items() if p != 0}
        require(not any(m & ((1 << (j + 1)) - 1) for m in value), "radical removal")
        trace.append({"conjugations": j + 1, "basis_terms": len(value),
                      "polynomial_terms": sum(len(p.terms) for p in value.values())})
    require(set(value) <= {0}, "formal norm is scalar")
    return value.get(0, Polynomial(0)), trace


def check_dag(dag):
    variables, ports = dag["variables"], dag["fixed_numerals"]
    require(len(variables) == len(set(variables)), "distinct DAG variables")
    require(len(ports) == len(set(ports)), "distinct DAG fixed numerals")
    require(not set(variables) & set(ports), "disjoint DAG inputs")
    leaves = set(variables) | set(ports)

    def ref(r, limit):
        require(isinstance(r, list) and len(r) == 2, "DAG reference format")
        if r[0] == "const":
            require(isinstance(r[1], int) and not isinstance(r[1], bool), "integer constant")
        elif r[0] == "leaf":
            require(r[1] in leaves, "declared DAG leaf")
        else:
            require(r[0] == "node" and isinstance(r[1], int) and 0 <= r[1] < limit,
                    "topologically earlier DAG node")

    for i, node in enumerate(dag["nodes"]):
        require(len(node) == 3 and node[0] in ("add", "sub", "mul"), "binary polynomial node")
        ref(node[1], i)
        ref(node[2], i)
    ref(dag["output"], len(dag["nodes"]))
    live, used = set(), set()

    def visit(r):
        if r[0] == "leaf":
            used.add(r[1])
        if r[0] != "node" or r[1] in live:
            return
        live.add(r[1])
        visit(dag["nodes"][r[1]][1])
        visit(dag["nodes"][r[1]][2])

    visit(dag["output"])
    counts = {op: sum(n[0] == op for n in dag["nodes"]) for op in ("add", "sub", "mul")}
    require(len(live) == len(dag["nodes"]) == dag["operations"], "all operations live")
    require(counts == dag["counts"], "binary operation counts")
    require(used == leaves, "every advertised input used")
    return counts


def dag_value(dag, env, *, degree=False, modulus=None):
    values = []

    def get(r):
        if r[0] == "const":
            return 0 if degree else r[1]
        if r[0] == "leaf":
            return env[r[1]]
        return values[r[1]]

    for op, left, right in dag["nodes"]:
        a, b = get(left), get(right)
        if degree:
            value = a + b if op == "mul" else max(a, b)
        else:
            value = a + b if op == "add" else a - b if op == "sub" else a * b
            if modulus is not None:
                value %= modulus
        values.append(value)
    return get(dag["output"])


def symbolic_checks(root):
    x, a, b, c, d, e = [Polynomial.variable(j) for j in range(6)]
    independent4, trace4 = formal_norm(x, [a, b, c, d])
    # Direct transcription of the displayed four-root formula, independent
    # of its code generator and of the conjugation computation above.
    p, q, u, v = a * b, c * d, a + b, c + d
    s = x * x - u - v
    K = s * s - 4 * u * v + 4 * (p + q)
    L, M, N = -4 * (s + 2 * v), -4 * (s + 2 * u), -8
    compact4 = (K * K + p * L * L - q * (M * M + p * N * N)) ** 2
    compact4 -= p * (2 * K * L - 2 * q * M * N) ** 2
    require(independent4 == compact4, "generic four-root coefficient identity")

    independent5, trace5 = formal_norm(x, [a, b, c, d, e])
    generic_path = root / "abstract_norm5_dag.json"
    generic = json.loads(generic_path.read_text())
    counts = check_dag(generic)
    require(generic["variables"] == ["x", "d0", "d1", "d2", "d3", "d4"], "abstract norm ports")
    compact5 = dag_value(generic, dict(zip(generic["variables"], [x, a, b, c, d, e])))
    require(independent5 == compact5, "generic five-root compact DAG coefficient identity")
    # The degree-reducing midpoint shift is verified as a universal
    # polynomial identity, before specializing H,Q,V to the source graph.
    H, Q, V = a, b, c
    midpoint = 8 * H * (2 * Q - 1) * V
    last_radicand = 256 * H * H * (Q - 1) * (Q * V * V - 1)
    midpoint_remainder = 64 * H * H * V * V + 256 * H * H * (Q - 1)
    require(midpoint * midpoint - last_radicand == midpoint_remainder,
            "exact auxiliary midpoint cancellation")
    return {"method": "Exact integer coefficient equality with independently computed formal multiquadratic conjugate products.",
            "four_root": {"terms": len(independent4.terms), "sha256": independent4.digest(), "trace": trace4},
            "five_root": {"terms": len(independent5.terms), "sha256": independent5.digest(), "trace": trace5},
            "generic_dag": {"sha256": hashlib.sha256(generic_path.read_bytes()).hexdigest(),
                            "operations": generic["operations"], "counts": counts},
            "midpoint_cancellation": "Exact integer polynomial identity L^2-rad4=K."}


def finalize(packet, rows):
    if packet["finalizer"] == "direct":
        require(len(rows) == 1, "direct residual census")
        return rows[0]
    if packet["finalizer"] == "sos":
        return sum(r * r for r in rows)
    require(packet["finalizer"] == "unit_product", "known finalizer")
    out = 1
    for r in rows:
        out *= 1 + 4 * r
    return out - 1


def audit_literal(root, path, constants):
    dag = json.loads(path.read_text())
    counts = check_dag(dag)
    packet_path = root / dag["source_packet"]
    packet = json.loads(packet_path.read_text())
    require(packet["variables"] == dag["variables"], "packet/DAG variables")
    require(packet["fixed_numerals"] == dag["fixed_numerals"], "packet/DAG fixed numerals")
    require(packet["variable_count"] == len(dag["variables"]), "literal variable census")
    require(packet["domain"] == dag["domain"] == "unrestricted integers", "literal domain")
    syntax_upper = dag_value(dag, {**{v: 1 for v in dag["variables"]},
                                   **{v: 0 for v in dag["fixed_numerals"]}}, degree=True)
    upper = syntax_upper
    if packet["name"] == "parity13_shifted":
        formulas = dict(packet["polynomial_abbreviations"])
        expected_formulas = {
            "delta": "Q-1", "r_aux": "Q*V**2-1", "Caux": "delta*r_aux",
            "Lshift": "8*H*(2*Q-1)*V",
            "Kshift": "64*H**2*V**2+256*H**2*delta",
            "Zbase": "H*x_parity+b0", "carrier": "Zbase+Lshift",
            "rad4": "256*H**2*Caux",
        }
        for name, formula in expected_formulas.items():
            require(formulas[name] == formula, "midpoint literal binding: " + name)
        degrees = {**{v: 1 for v in packet["variables"]},
                   **{v: 0 for v in packet["fixed_numerals"]}}
        for name, formula in packet["polynomial_abbreviations"]:
            degrees[name] = expression(formula, degrees, degree=True)
        radicand_degrees = [degrees["rad" + str(j)] for j in range(4)]
        require(all(d % 2 == 0 for d in radicand_degrees), "integral radical weights")
        root_weight = max(d // 2 for d in radicand_degrees)
        base_weight = max(degrees["Zbase"], root_weight)
        pair_weight = max(2 * base_weight, degrees["Lshift"] + base_weight, degrees["Kshift"])
        # Pairing the +/- last radical in the already proved norm identity
        # gives 16 factors (Z-S)^2+2L(Z-S)+K, each of this weighted degree.
        upper = 16 * pair_weight
        require(pair_weight == packet["degree_certificate"]["pair_factor_weighted_degree"],
                "midpoint pair weighted-degree bound")
        require(upper < syntax_upper, "midpoint cancellation improves the bound")
    require(upper == dag["exact_degree"] == packet["exact_degree"], "degree upper bound")
    cert = packet["degree_certificate"]
    require(cert["prime"] == Line.prime, "degree certificate prime")
    require(set(cert["slopes"]) == set(dag["variables"]), "degree slopes census")
    lines = {k: Line([0, v]) for k, v in cert["slopes"].items()}
    fixed_lines = {k: Line(v % Line.prime) for k, v in constants.items()}
    line = dag_value(dag, {**fixed_lines, **lines})
    require(len(line.c) - 1 == upper, "degree upper bound attained on actual-coefficient line")
    claimed_leader = cert.get("final_leading_coefficient_mod_prime", cert.get("leading_coefficient_mod_prime"))
    require(claimed_leader is not None and line.c[-1] == claimed_leader, "actual coefficient leader")

    diagnostics = 0
    rng = random.Random(2577 + len(dag["variables"]))
    for prime in (1000000007, 1000000009):
        fixed = {k: v % prime for k, v in constants.items()}
        for _ in range(64):
            vals = {v: rng.randrange(-2000, 2001) for v in dag["variables"]}
            _, rows = evaluate_packet(packet, vals, fixed, modulus=prime)
            expected = finalize(packet, rows) % prime
            actual = dag_value(dag, {**fixed, **vals}, modulus=prime)
            require(actual == expected, "literal DAG versus source packet")
            diagnostics += 1
    return {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "packet_sha256": hashlib.sha256(packet_path.read_bytes()).hexdigest(),
            "variables": len(dag["variables"]), "operations": dag["operations"], "counts": counts,
            "exact_degree": upper, "syntactic_degree_bound": syntax_upper,
            "actual_coefficient_leader_mod_prime": line.c[-1],
            "supplementary_modular_packet_agreement_checks": diagnostics}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    started = time.monotonic()
    symbolic = symbolic_checks(root)
    constants, coefficient_audit = load_coefficients(root)
    equations = {}
    for path in sorted(root.glob("*_dag.json")):
        if path.name.startswith(("parity", "centered")):
            equations[path.stem] = audit_literal(root, path, constants)
    require(equations, "literal equations present")
    result = {"status": "PASS", "scope": "Exact generic norm identities; literal DAG counts, liveness, syntax, coefficient binding, and exact degrees; modular packet agreement diagnostics.",
              "symbolic": symbolic, "coefficient_payloads": coefficient_audit, "equations": equations,
              "elapsed_seconds": round(time.monotonic() - started, 3)}
    output = args.output or root / "COMPACT_INDEPENDENT_AUDIT.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
