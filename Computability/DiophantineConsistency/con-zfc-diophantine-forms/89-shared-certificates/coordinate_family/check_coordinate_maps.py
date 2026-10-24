#!/usr/bin/env python3
"""Independent sparse algebra audit of the 21/20/19 integer-coordinate maps.

This script does not import the author's polynomial engine or generator.
It checks identities over Z[fixed_ports, variables], prior to any numerical
specialization of the fixed ports. Semantic calibration is a separate
inherited dependency, not proved by finite algebraic checks.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.setrecursionlimit(30000)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def constant(n):
    return {(): n} if n else {}


def symbol(name):
    return {(name,): 1}


def add(a, b, scale=1):
    out = defaultdict(int, a)
    for mon, value in b.items():
        out[mon] += scale * value
    return {mon: c for mon, c in out.items() if c}


def multiply(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return {mon: c for mon, c in out.items() if c}


def power(a, n):
    require(isinstance(n, int) and n >= 0, "invalid polynomial exponent")
    out = constant(1)
    while n:
        if n & 1:
            out = multiply(out, a)
        n //= 2
        if n:
            a = multiply(a, a)
    return out


def parse(text, env=None):
    env = env or {}
    def visit(node):
        if isinstance(node, ast.Constant):
            require(type(node.value) is int, "noninteger coefficient")
            return constant(node.value)
        if isinstance(node, ast.Name):
            return env[node.id] if node.id in env else symbol(node.id)
        if isinstance(node, ast.UnaryOp):
            require(isinstance(node.op, (ast.USub, ast.UAdd)), "unsupported unary operation")
            return {mon: (-c if isinstance(node.op, ast.USub) else c)
                    for mon, c in visit(node.operand).items()}
        require(isinstance(node, ast.BinOp), "unsupported polynomial syntax")
        if isinstance(node.op, (ast.Add, ast.Sub)):
            pending = [(node, 1)]
            out = defaultdict(int)
            while pending:
                term, sign = pending.pop()
                if isinstance(term, ast.BinOp) and isinstance(term.op, (ast.Add, ast.Sub)):
                    pending.append((term.left, sign))
                    pending.append((term.right, -sign if isinstance(term.op, ast.Sub) else sign))
                else:
                    for mon, c in visit(term).items():
                        out[mon] += sign * c
            return {mon: c for mon, c in out.items() if c}
        if isinstance(node.op, ast.Mult):
            return multiply(visit(node.left), visit(node.right))
        if isinstance(node.op, ast.Pow):
            require(isinstance(node.right, ast.Constant) and type(node.right.value) is int,
                    "nonliteral exponent")
            return power(visit(node.left), node.right.value)
        raise AssertionError("nonpolynomial operation")
    return visit(ast.parse(text, mode="eval").body)


def substitute(poly, replacements):
    out = {}
    cache = {}
    for mon, coefficient in poly.items():
        value = constant(coefficient)
        for name, exponent in Counter(mon).items():
            key = (name, exponent)
            if key not in cache:
                cache[key] = power(replacements.get(name, symbol(name)), exponent)
            value = multiply(value, cache[key])
        out = add(out, value)
    return out


def degree(poly, variables):
    variables = set(variables)
    return max((sum(v in variables for v in mon) for mon in poly), default=0)


def square_coefficient(poly, target, variables):
    variables = set(variables)
    groups = {}
    for mon, coefficient in poly.items():
        unknowns = tuple(v for v in mon if v in variables)
        counts = Counter(unknowns)
        if any(count > target.get(v, 0) for v, count in counts.items()):
            continue
        ports = tuple(v for v in mon if v not in variables)
        groups[unknowns] = add(groups.get(unknowns, {}), {ports: coefficient})
    result = {}
    for mon, coefficients in groups.items():
        counts = Counter(mon)
        other = tuple(sorted(v for v, count in target.items()
                             for _ in range(count - counts[v])))
        result = add(result, multiply(coefficients, groups.get(other, {})))
    return result


def read_packet(path):
    data = json.loads(path.read_text())
    rows = [parse(row) for row in data["residuals"]]
    return data, rows


def audit(root):
    files = [root / "incoming_joint25.json", root / "equations/octic25.json",
             root / "equations/compact_octic25.json"]
    files += [root / "equations" / name for name in
              ("coordinate21_degree16.json", "coordinate20_degree18.json",
               "coordinate19_degree40.json")]
    incoming, incoming_rows = read_packet(files[0])
    parent, parent_rows = read_packet(files[1])
    compact = json.loads(files[2].read_text())
    aliases = {}
    for name, expression in compact["definitions"].items():
        aliases[name] = parse(expression, aliases)
    require([parse(row, aliases) for row in compact["residuals"]] == parent_rows,
            "compact parent differs from literal parent")

    reorder = [0, 1, 2, 3, 4, 5, 6, 7, 11, 8, 9, 10, 12]
    aligned = [incoming_rows[i] for i in reorder]
    bridge = {2: parse("E-a"), 3: parse("-E*(c-eta)"), 5: constant(1)}
    for i, ours in enumerate(parent_rows):
        require(ours == add(aligned[i], multiply(bridge.get(i, {}), incoming_rows[11])),
                "incoming unimodular bridge row " + str(i))

    q = parse("beta*(3*J3+1)+1")
    # Check the four coordinate swaps before restricting to any zero set.
    old_to_new = {"C": add(add(q, symbol("F"), -1), symbol("alpha"), -1),
                  "Y": parse("a-E"), "k": parse("eta+zeta"),
                  "tau_gap": parse("tau-E*(c-eta)")}
    inverse = {"alpha": add(add(q, symbol("F"), -1), symbol("C"), -1),
               "a": parse("E+Y"), "zeta": parse("k-eta"),
               "tau": parse("tau_gap+E*(c-eta)")}
    for name, polynomial in inverse.items():
        require(substitute(polynomial, old_to_new) == symbol(name),
                "triangular coordinate inverse " + name)

    literal_definitions = [
        ("J0", "3*J3+1"), ("W", "4*(3*w3+1)"), ("q", "beta*J0+1"),
        ("X", "W*q"), ("Fbar", "(K0+W)*C-z*(q-1)"), ("Ebar", "X*Y"),
        ("abar", "Ebar+Y"), ("etabar", "c-Y*k"), ("zetabar", "k-etabar"),
        ("Vbar", "f*o-c")]
    aliases = {}
    for name, expression in literal_definitions:
        aliases[name] = parse(expression, aliases)
    restoration21 = {name: parse(expression, aliases) for name, expression in {
        "F": "Fbar", "alpha": "q-Fbar-C", "a": "abar", "E": "Ebar",
        "eta": "etabar", "zeta": "zetabar", "V": "Vbar",
        "tau": "tau_gap+Ebar*Y*k"}.items()}
    data21, rows21 = read_packet(files[3])
    transformed = []
    for i, row in enumerate(parent_rows):
        row = substitute(row, restoration21)
        if i in {1, 2, 6, 7}:
            require(not row, "deleted defining row in 21 map")
        else:
            transformed.append(row)
    require(transformed == rows21, "21-coordinate restoration row identity")

    data20, rows20 = read_packet(files[4])
    restoration20 = {"I": parse("(2*r+1)*c**2"), "y": parse("f*o+y_gap")}
    transformed = []
    for i, row in enumerate(rows21):
        row = substitute(row, restoration20)
        if i == 5:
            require(not row, "deleted I row")
        else:
            transformed.append(row)
    require(transformed == rows20, "20-coordinate restoration row identity")
    require(parse("(f*o+y_gap)**2-(f*o-c)**2") ==
            parse("(c+y_gap)*(2*f*o+y_gap-c)"), "auxiliary root cancellation")

    data19, rows19 = read_packet(files[5])
    restoration19 = {"Y": multiply(parse("2*v_scale+1"), power(q, 3))}
    transformed = []
    for i, row in enumerate(rows20):
        row = substitute(row, restoration19)
        if i == 0:
            require(not row, "deleted Y row")
        else:
            transformed.append(row)
    require(transformed == rows19, "19-coordinate restoration row identity")

    summary = []
    for data, rows, wanted, expected in [
        (data21, rows21, {"Y": 8, "k": 8}, "1"),
        (data20, rows20, {"r": 4, "c": 10, "f": 2, "o": 2}, "64"),
        (data19, rows19, {"v_scale": 8, "J3": 24, "k": 8}, "2**8*3**24*beta**24")]:
        variables = data["variables"]
        require(data["domain"] == "unrestricted integers", "integer domain")
        require(len(variables) == len(set(variables)) == data["variable_count"], "variable count")
        live = set(v for row in rows for mon in row for v in mon)
        require(set(variables) <= live, "unused variable")
        require(live <= set(variables + data["fixed_ports"]), "unbound symbol")
        degrees = [degree(row, variables) for row in rows]
        require(degrees == data["residual_degrees"], "residual degree census")
        certificate = {}
        for row in rows:
            certificate = add(certificate, square_coefficient(row, wanted, variables))
        require(certificate == parse(expected), "leading coefficient certificate")
        require(2 * max(degrees) == sum(wanted.values()) == data["exact_degree"],
                "exact degree conclusion")
        summary.append(dict(variables=len(variables), rows=len(rows),
                            residual_degrees=degrees, exact_degree=data["exact_degree"],
                            degree_certificate=expected,
                            literal_algebra_and_integer_restoration="PASS"))
    return dict(status="PASS", optimized=not __debug__, results=summary,
                parent_compact_expansion="PASS", incoming_row_permutation=reorder,
                incoming_quotient_row_zero_based=11,
                incoming_unimodular_bridge="PASS", triangular_inverse_identities=4,
                inherited_semantic_calibration_reproved=False,
                file_sha256={str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest() for p in files},
                scope="Exact polynomial identities and unrestricted-integer restoration maps, not a new native/compiler or ZFC calibration proof")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", type=Path, required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    result = audit(args.directory)
    result["checker_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
