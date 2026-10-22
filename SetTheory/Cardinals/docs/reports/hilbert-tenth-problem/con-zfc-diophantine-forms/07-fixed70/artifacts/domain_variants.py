#!/usr/bin/env python3
"""Emit explicit nonnegative- and integer-domain variants of fixed70.

Python 3 standard library only. The adjacent fixed_input.json is the only
input artifact. The fixed compiler coefficients retain their exact finite
specification; small arithmetic fixtures below are not compiler instances.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from random import Random


PARENT_FILE_SHA256 = "a8042fde1907a58623c21c6cacf390039e6b44c22152281fd0032a298557c464"
PARENT_SOURCE_SHA256 = "458aa30130504edf7e00b6a4aea294a6dbab110d904032d19ff8803a651ad96f"
DEGREE_PROOF = (
    "Let H be the nonzero degree-169 leading homogeneous form of fixed70 "
    "for the prescribed fixed coefficients. Translating each variable by 1 "
    "preserves H and hence the degree 169. Under v=1+sum_{j=1}^4 u_{v,j}^2, "
    "the degree-338 homogeneous part is H(sum_j u_{1,j}^2,...,sum_j u_{16,j}^2). "
    "Setting coordinates 2,3,4 in every group to zero gives "
    "H(u_{1,1}^2,...,u_{16,1}^2), which is nonzero: doubling each exponent "
    "is an injective map on monomials. Thus the integer variant has exact "
    "degree 338, not only an upper bound."
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def make_variant(parent, integer_domain):
    """Prepend substitutions, retaining all original rows verbatim."""
    rows = []
    witnesses = []
    substitution = {}
    for old in parent["witnesses"]:
        if integer_domain:
            variables = ["u_%s_%d" % (old, j) for j in range(1, 5)]
            squares = ["four_square_%s_%d" % (old, j) for j in range(1, 5)]
            witnesses.extend(variables)
            substitution[old] = variables
            rows.extend([square, "*", variable, variable]
                        for square, variable in zip(squares, variables))
            partial12 = "four_sum_%s_12" % old
            partial123 = "four_sum_%s_123" % old
            partial1234 = "four_sum_%s_1234" % old
            rows.extend([
                [partial12, "+", squares[0], squares[1]],
                [partial123, "+", partial12, squares[2]],
                [partial1234, "+", partial123, squares[3]],
                [old, "+", partial1234, 1],
            ])
        else:
            variable = "n_" + old
            witnesses.append(variable)
            substitution[old] = [variable]
            rows.append([old, "+", variable, 1])
    wrapper_rows = len(rows)
    rows.extend([list(row) for row in parent["source"]])
    return {
        "name": "fixed70_integer64" if integer_domain else "fixed70_nonnegative16",
        "witness_domain": "integers" if integer_domain else "nonnegative integers",
        "witnesses": witnesses,
        "fixed_numerals": list(parent["fixed_numerals"]),
        "source": rows,
        "output": parent["output"],
        "exact_degree": 338 if integer_domain else 169,
        "parent_packet": parent["name"],
        "parent_source_sha256": digest(parent["source"]),
        "substitution": substitution,
        "substitution_rule": "v = 1 + sum(u*u for u in substitution[v])"
                             if integer_domain else "v = substitution[v][0] + 1",
        "wrapper_row_count": wrapper_rows,
        "degree_proof": DEGREE_PROOF,
        "scope": (
            "Exact direct domain conversion of fixed70 with the same five fixed "
            "compiler numerals. All rows are included. No further optimization "
            "or global minimality claim."
        ),
    }


def evaluate(packet, values):
    ports = packet["witnesses"] + packet["fixed_numerals"]
    require(set(values) == set(ports), "assignment has wrong ports")
    require(all(type(value) is int for value in values.values()), "exact integer values required")
    result = dict(values)
    for name, operator, left, right in packet["source"]:
        a = left if type(left) is int else result[left]
        b = right if type(right) is int else result[right]
        if operator == "+":
            result[name] = a + b
        elif operator == "-":
            result[name] = a - b
        else:
            require(operator == "*", "unknown operator")
            result[name] = a * b
    return result


def structure(packet):
    ports = packet["witnesses"] + packet["fixed_numerals"]
    require(len(ports) == len(set(ports)), "duplicate ports")
    seen = set(ports)
    degrees = {name: 1 for name in packet["witnesses"]}
    degrees.update({name: 0 for name in packet["fixed_numerals"]})
    dependencies = {}
    multiplication = addition = 0
    for row in packet["source"]:
        require(type(row) is list and len(row) == 4, "bad source row")
        name, operator, left, right = row
        require(type(name) is str and name not in seen, "duplicate or invalid output")
        require(operator in {"+", "-", "*"}, "bad operator")
        require(all(type(value) is int or (type(value) is str and value in seen)
                    for value in (left, right)), "forward reference or invalid operand")
        ld = 0 if type(left) is int else degrees[left]
        rd = 0 if type(right) is int else degrees[right]
        degrees[name] = ld + rd if operator == "*" else max(ld, rd)
        dependencies[name] = {value for value in (left, right) if type(value) is str}
        seen.add(name)
        multiplication += operator == "*"
        addition += operator != "*"
    require(packet["output"] in dependencies, "missing output")
    live = {packet["output"]}
    queue = list(live)
    while queue:
        for dependency in dependencies.get(queue.pop(), ()):
            if dependency not in live:
                live.add(dependency)
                queue.append(dependency)
    require(set(dependencies) <= live, "dead source row")
    require(set(ports) <= live, "dead input port")
    return {
        "M": multiplication,
        "A": addition,
        "total": multiplication + addition,
        "witnesses": len(packet["witnesses"]),
        "equations": 1,
        "exact_degree": packet["exact_degree"],
        "gate_degree_upper_bound": degrees[packet["output"]],
        "source_sha256": digest(packet["source"]),
    }


def verify(input_path=None):
    path = Path(input_path) if input_path is not None else Path(__file__).with_name("fixed_input.json")
    parent_bytes = path.read_bytes()
    require(hashlib.sha256(parent_bytes).hexdigest() == PARENT_FILE_SHA256,
            "fixed_input.json hash differs from pinned parent")
    receipt = json.loads(parent_bytes)
    candidates = [packet for packet in receipt["packets"] if packet["name"] == "fixed70"]
    require(len(candidates) == 1, "fixed70 packet missing or duplicated")
    parent = candidates[0]
    require(digest(parent["source"]) == PARENT_SOURCE_SHA256, "fixed70 source hash mismatch")
    require(parent["witness_domain"] == "strictly positive integers", "wrong parent domain")
    require(parent["exact_degree"] == 169, "wrong parent degree")
    packets = [make_variant(parent, False), make_variant(parent, True)]
    reports = {packet["name"]: structure(packet) for packet in packets}
    expected = ((40, 46, 86, 16, 169), (104, 94, 198, 64, 338))
    for packet, wanted in zip(packets, expected):
        metric = reports[packet["name"]]
        actual = tuple(metric[key] for key in ("M", "A", "total", "witnesses", "exact_degree"))
        require(actual == wanted, "domain-variant metrics mismatch")
        require(packet["source"][packet["wrapper_row_count"]:] == parent["source"],
                "original rows changed")

    rng = Random(215)
    numerals = dict(zip(parent["fixed_numerals"], (15, 29, 2, 35, 67)))
    fixture_count = 32
    for packet in packets:
        integer_domain = packet["witness_domain"] == "integers"
        for trial in range(fixture_count):
            values = {
                name: 0 if trial == 0 else rng.randrange(-4 if integer_domain else 0, 5)
                for name in packet["witnesses"]
            }
            values.update(numerals)
            positive = dict(numerals)
            for old, variables in packet["substitution"].items():
                positive[old] = 1 + sum(values[name]**2 for name in variables) if integer_domain else values[variables[0]] + 1
                require(positive[old] > 0, "substitution failed positivity")
            converted = evaluate(packet, values)
            original = evaluate(parent, positive)
            require(all(converted[name] == original[name] for name in parent["witnesses"]),
                    "substitution register mismatch")
            require(all(converted[row[0]] == original[row[0]] for row in parent["source"]),
                    "converted arithmetic differs from original arithmetic")

    return {
        "status": "PASS",
        "parent": {
            "file": "fixed_input.json",
            "file_sha256": PARENT_FILE_SHA256,
            "packet": "fixed70",
            "source_sha256": PARENT_SOURCE_SHA256,
        },
        "circuits": reports,
        "identity_fixture_count_per_variant": fixture_count,
        "identity_scope": (
            "For each variant, compare every original witness and all 70 original "
            "registers with direct evaluation after the stated substitution. "
            "Include the all-zero new-witness assignment and 31 seeded assignments. "
            "Small fixed numeral choices test arithmetic only, not compiler validity."
        ),
        "degree_proof": DEGREE_PROOF,
        "proof_boundary": (
            "The generator checks the source hash, circuit dependencies, liveness, "
            "counts, verbatim preservation of the parent rows, and exact arithmetic "
            "fixtures. The domain equivalence uses the stated substitutions and "
            "Lagrange's four-square theorem. Exact degrees use the parent's proved "
            "nonzero leading form and the injective substitution argument. These "
            "checks neither instantiate huge compiler numerals nor verify or decide "
            "ZFC consistency."
        ),
        "packets": packets,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=Path(__file__).with_name("fixed_input.json"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = verify(args.input)
    if args.output is not None:
        args.output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "circuits": receipt["circuits"]}, indent=2))


if __name__ == "__main__":
    main()
