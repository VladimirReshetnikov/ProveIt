#!/usr/bin/env python3
"""A complete84 regrouping and exact evidence for a generic four-port cut.

Only authenticated data are read. No predecessor Python is imported or run.
The circuit lower bound is proved in the companion note, not by enumeration.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path


PINS = {
    "complete84_scaled_strong_output.py": "8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737",
    "complete84_scaled_strong_output.json": "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf",
    "complete84_scaled_strong_output.md": "01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade",
    "complete84_local_producer_scout.py": "472f6d1afba2cbc138d7be94dba1004031ac92b9af458ed1a3099d4393736194",
    "complete84_local_producer_scout.json": "a03d2a2704a937223836e12fd38c9d8516e92a845aeed70377cdacac58b7d4ca",
    "complete84_local_producer_scout.md": "7cfa58529ec02a6cf3df475e3d0feda6b4e5f4ad6b6c622e810907371b0aecad",
}
OLD_TAIL = [
    ["norm_pair", "*", "norm_first", "norm_main"],
    ["norm_triple", "*", "norm_pair", "norm_input"],
    ["norm_four", "*", "norm_triple", "norm_aux"],
    ["norm_product", "*", "norm_four", "norm_index"],
    ["all_units", "*", "norm_product", "norm_transport"],
    ["seven_units", "*", "all_units", "norm_strong"],
    ["polynomial", "-", "seven_units", "A"],
]
NEW_TAIL = [
    ["joint_aux_strong", "*", "norm_aux", "norm_strong"],
    ["norm_pair", "*", "norm_first", "norm_main"],
    ["norm_triple", "*", "norm_pair", "norm_input"],
    ["norm_product", "*", "norm_triple", "norm_index"],
    ["all_units", "*", "norm_product", "norm_transport"],
    ["seven_units", "*", "all_units", "joint_aux_strong"],
    ["polynomial", "-", "seven_units", "A"],
]
BLOCK = [
    ["norm_strong", "-", "scaled_f_square", "R16"],
    ["aux_square_gap", "-", "H2", "aux_y2"],
    ["L17", "*", "R16", "aux_square_gap"],
    ["norm_aux", "+", "L17", "aux_y2"],
    ["joint_aux_strong", "*", "norm_aux", "norm_strong"],
]
CUTS = ["scaled_f_square", "R16", "H2", "aux_y2"]
FACTOR_PORTS = [
    "norm_first", "norm_main", "norm_input", "norm_aux",
    "norm_index", "norm_transport", "norm_strong", "A",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def no_duplicates(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "duplicate JSON key: " + key)
        out[key] = value
    return out


def invalid_constant(value):
    raise ValueError("nonfinite JSON number: " + value)


def read_json(raw):
    return json.loads(raw, object_pairs_hook=no_duplicates, parse_constant=invalid_constant)


def exact_equal(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(exact_equal(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact_equal(a, b) for a, b in zip(left, right))
    return left == right


def graph(source, free, output):
    require(len(set(free)) == len(free), "duplicate supplied port")
    available = set(free)
    definitions = {}
    for row in source:
        require(type(row) is list and len(row) == 4, "bad source row")
        name, op, left, right = row
        require(type(name) is str and name not in available, "redefined register")
        require(op in ("+", "-", "*"), "unsupported operation")
        for operand in (left, right):
            require(type(operand) is int or type(operand) is str and operand in available,
                    "unbound or invalid operand")
        available.add(name)
        definitions[name] = row
    require(output in definitions, "missing output")
    live, todo = set(), [output]
    while todo:
        name = todo.pop()
        if name in live:
            continue
        live.add(name)
        if name in definitions:
            todo.extend(x for x in definitions[name][2:] if type(x) is str)
    require(live == available, "dead gate or unused supplied port")
    operations = Counter(row[1] for row in source)
    return {"M": operations["*"], "A": operations["+"] + operations["-"],
            "total": len(source), "live_gates": len(definitions), "live_free_ports": len(free)}


def evaluate(source, values):
    env = dict(values)
    for name, op, left, right in source:
        a = env[left] if type(left) is str else left
        b = env[right] if type(right) is str else right
        env[name] = a + b if op == "+" else a - b if op == "-" else a * b
    return env


def var(n, index):
    exponent = [0] * n
    exponent[index] = 1
    return {tuple(exponent): 1}


def add(left, right, sign=1):
    out = dict(left)
    for exponent, coefficient in right.items():
        out[exponent] = out.get(exponent, 0) + sign * coefficient
        if out[exponent] == 0:
            del out[exponent]
    return out


def mul(left, right):
    out = {}
    for e, c in left.items():
        for f, d in right.items():
            exponent = tuple(a + b for a, b in zip(e, f))
            out[exponent] = out.get(exponent, 0) + c * d
    return {e: c for e, c in out.items() if c}


def polynomial_source(source, ports):
    n = len(ports)
    env = {name: var(n, i) for i, name in enumerate(ports)}
    for name, op, left, right in source:
        a = env[left] if type(left) is str else ({(0,) * n: left} if left else {})
        b = env[right] if type(right) is str else ({(0,) * n: right} if right else {})
        env[name] = mul(a, b) if op == "*" else add(a, b, -1 if op == "-" else 1)
    return env


def terms(poly):
    return [[list(exponent), coefficient] for exponent, coefficient in sorted(poly.items())]


def build(root):
    raw = {}
    for name, digest in PINS.items():
        raw[name] = (root / name).read_bytes()
        require(sha(raw[name]) == digest, "dependency pin mismatch: " + name)
    parent_receipt = read_json(raw["complete84_scaled_strong_output.json"])
    require(parent_receipt["source_sha256"] == PINS["complete84_scaled_strong_output.py"],
            "parent self-source pin")
    parent = parent_receipt["packet"]
    source = parent["source"]
    old_names = {row[0] for row in OLD_TAIL}
    require([row for row in source if row[0] in old_names] == OLD_TAIL, "parent finalizer drift")
    core = [row for row in source if row[0] not in old_names]
    grouped = core + NEW_TAIL
    require(len(core) == 77, "producer core count")
    definitions = {row[0]: row for row in grouped}
    require(all(definitions[row[0]] == row for row in BLOCK), "joint block drift")
    require(definitions["scaled_f_square"] == ["scaled_f_square", "*", "A", "L16"], "scaled f square")
    require(definitions["R16"] == ["R16", "*", "aux_coefficient_root", "aux_coefficient_root"], "coefficient square")
    require(definitions["H2"] == ["H2", "*", "aux_u_rhs", "aux_u_rhs"], "auxiliary square")
    require(definitions["aux_y2"] == ["aux_y2", "*", "y_aux", "y_aux"], "y square")
    consumers = {name: [row[0] for row in grouped if name in row[2:]] for name in [row[0] for row in BLOCK]}
    require(consumers == {
        "norm_strong": ["joint_aux_strong"], "aux_square_gap": ["L17"],
        "L17": ["norm_aux"], "norm_aux": ["joint_aux_strong"],
        "joint_aux_strong": ["seven_units"],
    }, "joint block consumer closure")
    parent_ledger = graph(source, parent["free"], parent["output"])
    new_ledger = graph(grouped, parent["free"], parent["output"])
    require(parent_ledger == new_ledger == {"M": 47, "A": 37, "total": 84,
            "live_gates": 84, "live_free_ports": 25}, "complete ledger")
    require(len(parent["witnesses"]) == 18, "witness count")
    require(parent["free"] == parent["witnesses"] + ["x"] + parent["fixed_numerals"], "free interface")
    require(parent["factor_exact_degrees"] == [22, 18, 32, 60, 7, 2, 46], "parent factor degrees")
    require(parent["exact_degree"] == 187, "parent exact degree")

    old_poly = polynomial_source(OLD_TAIL, FACTOR_PORTS)["polynomial"]
    new_poly = polynomial_source(NEW_TAIL, FACTOR_PORTS)["polynomial"]
    expected = {tuple([1] * 7 + [0]): 1, tuple([0] * 7 + [1]): -1}
    require(old_poly == new_poly == expected, "entire factor finalizer identity")
    cut = polynomial_source(BLOCK, CUTS)["joint_aux_strong"]
    a, q, v, y = [var(4, i) for i in range(4)]
    explicit = mul(add(a, q, -1), add(mul(q, add(v, y, -1)), y))
    require(cut == explicit, "joint cut coefficient identity")
    require(len(cut) == 6, "joint cut support")
    cubic = {e: c for e, c in cut.items() if sum(e) == 3}
    require(cubic == mul(mul(q, add(a, q, -1)), add(v, y, -1)), "cubic leader identity")
    support = [(1, 1, 1, 0), (1, 1, 0, 1), (1, 0, 0, 1)]
    require(all(e in cut for e in support), "noncollinear support terms")
    differences = [[e[i] - support[0][i] for i in range(4)] for e in support[1:]]
    determinant = differences[0][1] * differences[1][2] - differences[0][2] * differences[1][1]
    require(determinant == -1, "Newton support noncollinearity")

    # Whole-source tests supplement the exact coefficient cuts and literal proof.
    values_digest = hashlib.sha256()
    for case in range(32):
        inputs = {}
        for i, port in enumerate(parent["free"]):
            numerator = ((case + 3) * (i + 5) + i * i) % 17 - 8
            inputs[port] = numerator if case < 16 else Fraction(numerator, 1 + ((case + i) % 4))
        old_env = evaluate(source, inputs)
        new_env = evaluate(grouped, inputs)
        for row in core:
            require(old_env[row[0]] == new_env[row[0]], "retained computed value")
        require(old_env["polynomial"] == new_env["polynomial"], "whole numeric identity")
        require(new_env["joint_aux_strong"] == old_env["norm_aux"] * old_env["norm_strong"], "joint numeric identity")
        value = Fraction(new_env["polynomial"])
        values_digest.update(canonical([case, str(value.numerator), str(value.denominator)]))

    packet = {
        "source": grouped, "output": "polynomial", "free": parent["free"],
        "witnesses": parent["witnesses"], "witness_domain": parent["witness_domain"],
        "ordinary_input": "x", "fixed_numerals": parent["fixed_numerals"],
        "ledger": {"M": 47, "A": 37, "total": 84, "producer_M": 41, "producer_A": 36,
                   "producer_total": 77, "finalizer_M": 6, "finalizer_A": 1, "finalizer_total": 7},
        "grouped_factors": ["norm_first", "norm_main", "norm_input", "norm_index", "norm_transport", "joint_aux_strong"],
        "grouped_factor_exact_degrees": [22, 18, 32, 7, 2, 106], "exact_degree": 187,
        "degree_provenance": "Inherited unchanged whole polynomial; degree106 is the sum60+46 in an integral domain.",
        "relation_to_complete84": "Identical entire polynomial over every commutative ring.",
        "coordinate_map": "identity", "same_positive_zero_tuples": True,
        "same_signed_zero_tuples": True,
        "scope": "A regrouping of the existing84 polynomial, with the identical inherited fixed-program recipe; no new universal upper bound.",
    }
    return {
        "status": "PASS", "source_sha256": sha(Path(__file__).read_bytes()), "pins": PINS,
        "scope": "Exact five-gate lower bound for the independent four-port joint polynomial only; complete actual source remains84.",
        "packet": packet,
        "source_checks": {"unchanged_producer_rows": len(core), "parent_ledger": parent_ledger,
                          "regrouped_ledger": new_ledger, "block_consumers": consumers,
                          "parent_source_sha256": sha(canonical(source)), "regrouped_source_sha256": sha(canonical(grouped)),
                          "finalizer_terms": terms(old_poly)},
        "cut": {"ports": CUTS, "formal_variables": ["A0", "Q", "V0", "Y0"], "source": BLOCK,
                "polynomial": "(A0-Q)*(Q*(V0-Y0)+Y0)", "terms": terms(cut), "cubic_leader_terms": terms(cubic),
                "support_points": [list(e) for e in support], "support_difference_minor_Q_V0": determinant,
                "upper_ledger": {"M": 2, "A": 3, "total": 5}, "minimum_gates": 5,
                "lower_bound_provenance": "Companion characteristic-zero normal-form and irreducibility proof; no finite census claim."},
        "numeric": {"whole_source_assignments": 32, "signed_integer": 16, "signed_rational": 16,
                    "whole_row_evaluations": 32 * 168, "retained_row_equalities": 32 * 77,
                    "output_digest": values_digest.hexdigest(), "full_positive_pell_witnesses_materialized": 0},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--expect", type=Path)
    args = parser.parse_args()
    receipt = build(args.root.resolve())
    encoded = json.dumps(receipt, indent=2, sort_keys=True, allow_nan=False) + "\n"
    require(exact_equal(receipt, read_json(encoded)), "typed JSON roundtrip")
    if args.expect is not None:
        require(exact_equal(receipt, read_json(args.expect.read_bytes())), "receipt mismatch")
    else:
        args.output.write_text(encoded)
    print("PASS: complete84 regrouping; generic joint cut5=2M+3A;32 whole-source assignments")


if __name__ == "__main__":
    main()
