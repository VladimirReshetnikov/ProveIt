#!/usr/bin/env python3
"""Check literal packets, fixed payloads and exact degree certificates.

Does not import the source builder. Expression evaluation uses a restricted
AST and a separate dense univariate polynomial implementation over F_p.
The generic norm/restoration identities are proved in independent_checks.py.
"""

from __future__ import annotations

import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Line:
    prime = 1000000007

    def __init__(self, values=0):
        data = [values] if isinstance(values, int) else list(values)
        self.c = [a % self.prime for a in data]
        while len(self.c) > 1 and self.c[-1] == 0:
            self.c.pop()

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Line) else Line(other)

    def __add__(self, other):
        other = self.coerce(other)
        data = [0] * max(len(self.c), len(other.c))
        for i, v in enumerate(self.c):
            data[i] += v
        for i, v in enumerate(other.c):
            data[i] += v
        return Line(data)

    __radd__ = __add__

    def __neg__(self):
        return Line([-x for x in self.c])

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        data = [0] * (len(self.c) + len(other.c) - 1)
        for i, a in enumerate(self.c):
            for j, b in enumerate(other.c):
                data[i + j] += a * b
        return Line(data)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, "invalid fixed exponent")
        out = Line(1)
        for _ in range(exponent):
            out *= self
        return out


def expression(text, environment, degree=False, modulus=None):
    node = ast.parse(text, mode="eval").body

    def visit(n):
        if isinstance(n, ast.Constant):
            require(isinstance(n.value, int) and not isinstance(n.value, bool), "noninteger constant")
            return 0 if degree else n.value
        if isinstance(n, ast.Name):
            require(n.id in environment, "undeclared input: " + n.id)
            return environment[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            v = visit(n.operand)
            return v if degree else -v
        require(isinstance(n, ast.BinOp), "forbidden expression node")
        if isinstance(n.op, ast.Pow):
            require(isinstance(n.right, ast.Constant) and isinstance(n.right.value, int) and n.right.value >= 0,
                    "nonliteral exponent")
            v = visit(n.left)
            result = v * n.right.value if degree else v ** n.right.value
        else:
            left, right = visit(n.left), visit(n.right)
            if isinstance(n.op, ast.Add):
                result = max(left, right) if degree else left + right
            elif isinstance(n.op, ast.Sub):
                result = max(left, right) if degree else left - right
            elif isinstance(n.op, ast.Mult):
                result = left + right if degree else left * right
            else:
                raise ValueError("forbidden arithmetic operation")
        if modulus is not None and not degree:
            result %= modulus
        return result

    return visit(node)


def load_coefficients(root):
    binding_path = root / "coefficients/BINDING.json"
    binding = json.loads(binding_path.read_text())
    values, audit = {}, {}
    for name, metadata in sorted(binding["ports"].items()):
        packed = (binding_path.parent / metadata["file"]).read_bytes()
        raw = gzip.decompress(packed)
        require(hashlib.sha256(packed).hexdigest() == metadata["sha256_gzip"], name + " gzip digest")
        require(hashlib.sha256(raw).hexdigest() == metadata["sha256_raw"], name + " raw digest")
        value = int.from_bytes(raw, "little")
        require(value > 0 and value.bit_length() == metadata["bits"], name + " bit length")
        require(len(packed) == metadata["gzip_bytes"] and len(raw) == metadata["raw_bytes"], name + " length")
        require(len(raw) == (value.bit_length() + 7) // 8, name + " minimal representation")
        values[name] = value
        audit[name] = {"raw_sha256": metadata["sha256_raw"], "bits": value.bit_length()}
    require(values["beta"] == (1 << 1064921) - 1, "literal beta")
    require(values["cone_A"] == 1 << 1113, "first determinant constant")
    require(values["cone_B"] == 1 << 666104, "second determinant constant")
    require(sum(p["raw_bytes"] for p in binding["ports"].values()) == binding["raw_bytes_total"], "raw total")
    return values, audit


def evaluate_packet(packet, variables, constants, modulus=None):
    env = {**constants, **variables}
    for name, formula in packet["polynomial_abbreviations"]:
        require(name not in env, "shadowed port: " + name)
        env[name] = expression(formula, env, modulus=modulus)
    residuals = [expression(formula, env, modulus=modulus) for formula in packet["factored_residuals"]]
    return env, residuals


def audit_packet(path, constants, parent, parent_hash):
    packet = json.loads(path.read_text())
    require(packet["parent_sha256"] == parent_hash, "parent hash in " + path.name)
    require(packet["domain"] == "unrestricted integers", "domain")
    variables = packet["variables"]
    require(len(variables) == len(set(variables)) == packet["variable_count"], "variable census")
    removed = {"tau", "y_gap"}
    if packet["variable_count"] == 15:
        removed.add("pair_pos3")
    require(set(variables) == set(parent["variables"]) - removed | {"t_parity"}, "projection ports")
    require(packet["polynomial_abbreviations"][:len(parent["polynomial_abbreviations"])] ==
            parent["polynomial_abbreviations"], "retained parent prefix")
    require(packet["factored_residuals"][:2] == parent["factored_residuals"][1:3], "retained Pell rows")
    if packet["variable_count"] == 16:
        require(packet["factored_residuals"][2] == parent["factored_residuals"][4], "retained guard row")

    cert = packet["degree_certificate"]
    require(cert["prime"] == Line.prime, "prime convention")
    slopes = cert["slopes"]
    require(set(slopes) == set(variables), "degree line port census")
    lines = {name: Line([0, slope]) for name, slope in slopes.items()}
    _, residual_lines = evaluate_packet(packet, lines, {k: Line(v % Line.prime) for k, v in constants.items()})

    degrees = {name: 1 for name in variables}
    degrees.update({name: 0 for name in packet["fixed_numerals"]})
    for name, formula in packet["polynomial_abbreviations"]:
        degrees[name] = expression(formula, degrees, degree=True)
    upper = [expression(formula, degrees, degree=True) for formula in packet["factored_residuals"]]
    actual = [len(v.c) - 1 for v in residual_lines]
    leading = [v.c[-1] for v in residual_lines]
    require(upper == actual == cert["residual_degree_bounds"], "exact residual degree: " + path.name)
    require(leading == cert["residual_leading_coefficients_mod_prime"], "residual leaders: " + path.name)
    if packet["finalizer"] == "sos":
        out = sum((r * r for r in residual_lines), Line(0))
        final_bound = 2 * max(upper)
    else:
        require(packet["finalizer"] == "unit_product", "unknown finalizer")
        out = Line(1)
        for r in residual_lines:
            out *= 1 + 4 * r
        out -= 1
        final_bound = sum(upper)
    require(len(out.c) - 1 == final_bound == cert["final_degree"] == packet["exact_degree"], "final degree")
    require(out.c[-1] == cert["final_leading_coefficient_mod_prime"], "final leader")

    rng = random.Random(6328 + packet["variable_count"])
    diagnostics = 0
    for prime in (1000000007, 1000000009):
        fixed = {k: v % prime for k, v in constants.items()}
        for _ in range(48):
            vals = {name: rng.randrange(-1000, 1001) for name in variables}
            env, _ = evaluate_packet(packet, vals, fixed, modulus=prime)
            if packet["variable_count"] == 16:
                t = env["t_parity"]
                if packet["name"].startswith("centered"):
                    t += 2 * env["z0"] * env["k"]
                independent = (env["delta"] * (t * (t + 1) - env["A4"]) - env["r_aux"]) ** 2
                independent -= env["A"] * env["delta"] * env["r_aux"]
                require((independent - env["norm16"]) % prime == 0, "literal pair binding")
            else:
                x, a, b, c = env["x_parity"], env["A"], 4 * env["B_guard"], 16 * env["Caux"]
                independent = ((x * x - a - b - c) ** 2 - 4 * (a * b + a * c + b * c)) ** 2
                independent -= 64 * a * b * c * x * x
                require((independent - 256 * env["norm15"]) % prime == 0, "literal triple binding")
            diagnostics += 1
    return {"file_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "variables": len(variables), "residual_degrees": actual,
            "exact_degree": final_bound, "actual_coefficient_leader_mod_prime": out.c[-1],
            "supplementary_modular_binding_diagnostics": diagnostics}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    values, coefficient_audit = load_coefficients(root)
    parent_bytes = (root / "parent/degree88_17.json").read_bytes()
    parent_hash = hashlib.sha256(parent_bytes).hexdigest()
    parent = json.loads(parent_bytes)
    checks = {}
    for path in sorted(root.glob("*.json")):
        if path.name.startswith(("parity15_", "parity16_", "centered16_")) and not path.name.endswith("_dag.json"):
            checks[path.stem] = audit_packet(path, values, parent, parent_hash)
    require(len(checks) == 6, "missing intended literal packet")
    result = {"status": "PASS", "scope": "Fixed bytes, closed polynomial syntax, retained parent rows, exact degree bounds and modular-line attainment; no builder imported.",
              "parent_sha256": parent_hash, "coefficients": coefficient_audit, "equations": checks}
    out = args.output or root / "GRAPH_AUDIT.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
