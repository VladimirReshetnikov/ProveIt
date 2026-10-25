#!/usr/bin/env python3
"""Stdlib-only single-rational rank circuit and exact Laurent audit.

Reads the frozen parent as inert JSON; imports no repository implementation.
Use --write to regenerate, or --check to compare all generated evidence.
"""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "candidates/one-page-complemented47-independent"
REMOVED = {"q2minus1", "rproduct", "qMF", "maskfactor", "mask", "R"}
NEW_ROWS = [
    ["q2minus1", "-", "q2", 1],
    ["shifted_gap", "+", "gap", "U"],
    ["rank_product", "*", "q2minus1", "shifted_gap"],
    ["rank_linear", "*", "J", "W"],
    ["R", "+", "rank_product", "rank_linear"],
]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def digest(raw):
    return {"bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def add(a, b, sign=1):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0) + sign * coefficient
        if not out[monomial]:
            del out[monomial]
    return out


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            monomial = tuple(x + y for x, y in zip(ma, mb))
            out[monomial] = out.get(monomial, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def census(rows, leaves, output):
    names = set(leaves)
    producers = {}
    for name, op, left, right in rows:
        need(name not in names and op in {"+", "-", "*"}, "unique typed gate")
        for operand in (left, right):
            need(type(operand) is int or operand in names, "backward reference")
        names.add(name)
        producers[name] = (left, right)
    used = set()
    pending = [output]
    while pending:
        node = pending.pop()
        if type(node) is int or node in used:
            continue
        used.add(node)
        pending.extend(producers.get(node, ()))
    need(used == names, "every operation and declared leaf is live")
    return dict(sorted(Counter(row[1] for row in rows).items()))


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    parent_raw = (HERE / "source/parent66.json").read_bytes()
    need(parent_raw == (PARENT / "polynomial.json").read_bytes(), "actual parent snapshot")
    parent = json.loads(parent_raw)
    old_rows = parent["source"]
    witnesses = parent["witnesses"]
    ports = ["beta", "K0", "MC", "MF"]
    need(len(witnesses) == 15 and parent["fixed_numerals"] == ports, "all source leaves")
    old_counts = census(old_rows, witnesses + ports, "polynomial")
    need(old_counts == {"*": 38, "+": 15, "-": 13}, "original 66-gate census")
    new_rows = []
    for row in old_rows:
        if row[0] == "R":
            new_rows.extend(NEW_ROWS)
        elif row[0] not in REMOVED:
            new_rows.append(row)
    new_counts = census(new_rows, witnesses + ["beta", "K0", "U", "W"], "polynomial")
    need(new_counts == {"*": 37, "+": 15, "-": 13}, "65 rational-leaf gates")
    need(len(old_rows) == 66 and len(new_rows) == 65, "exact operation counts")

    # Exact Laurent ring Z[J,F,...,gamma,beta,beta^-1,K0,MC,MF].
    variables = witnesses + ports
    zero = (0,) * len(variables)

    def const(n):
        return {zero: n} if n else {}

    def monomial(powers, coefficient=1):
        exponent = [0] * len(variables)
        for name, power in powers.items():
            exponent[variables.index(name)] = power
        return {tuple(exponent): coefficient}

    leaves = {name: monomial({name: 1}) for name in variables}
    leaves["U"] = monomial({"MF": 1, "beta": -1})
    leaves["W"] = add(leaves["MC"], leaves["MF"], -1)

    def exact_evaluator(rows, override=None):
        definitions = {name: (op, left, right) for name, op, left, right in rows}
        cache = dict(leaves)
        if override:
            cache.update(override)

        def evaluate(name):
            if type(name) is int:
                return const(name)
            if name not in cache:
                op, left, right = definitions[name]
                a, b = evaluate(left), evaluate(right)
                cache[name] = mul(a, b) if op == "*" else add(a, b, 1 if op == "+" else -1)
            return cache[name]
        return evaluate

    old_exact = exact_evaluator(old_rows)
    new_exact = exact_evaluator(new_rows)
    old_rank, new_rank = old_exact("R"), new_exact("R")
    need(old_rank == new_rank, "universal complete rank identity")
    need(all(all(power >= 0 for power in m) for m in new_rank), "rank integral coefficients")
    for cut in ("rank_product", "rank_linear"):
        need(all(all(power >= 0 for power in m) for m in new_exact(cut)),
             "integral coefficients after the sole rational gate: " + cut)
    # The equality at R composes with the exactly unchanged entire suffix.
    old_index = next(i for i, row in enumerate(old_rows) if row[0] == "R")
    new_index = next(i for i, row in enumerate(new_rows) if row[0] == "R")
    need(old_rows[old_index + 1:] == new_rows[new_index + 1:], "identical complete suffix")
    need([row for row in old_rows[:old_index] if row[0] not in REMOVED]
         == new_rows[:new_index - 4], "identical complete retained prefix")

    # Leading forms are exact sparse Laurent polynomials. All coefficient
    # ports have degree zero; all fifteen witnesses have degree one.
    def degree(poly):
        return max((sum(m[:15]) for m in poly), default=-1)

    def leading(poly):
        d = degree(poly)
        return {m: c for m, c in poly.items() if sum(m[:15]) == d}

    def degrees_and_leaders(rows):
        evaluate = exact_evaluator(rows)
        top = {name: leading(value) for name, value in leaves.items()}
        cancellations = []

        def get(name):
            return const(name) if type(name) is int else top[name]

        for name, op, left, right in rows:
            a, b = get(left), get(right)
            if op == "*":
                value = mul(a, b)
            elif degree(a) > degree(b):
                value = a
            elif degree(b) > degree(a):
                value = b if op == "+" else {m: -c for m, c in b.items()}
            else:
                value = add(a, b, 1 if op == "+" else -1)
                if not value:
                    exact = evaluate(name)
                    value = leading(exact)
                    cancellations.append({"gate": name, "exact_terms": len(exact),
                                          "apparent_degree": degree(a), "actual_degree": degree(value)})
            top[name] = value
        return top, cancellations

    top, cancellations = degrees_and_leaders(new_rows)
    expected = monomial({"beta": 91, "J": 91, "h": 1, "gamma": 1,
                         "i": 4, "w": 13, "s": 26, "T": 2, "f": 4}, -8)
    k0 = add(leaves["eta"], leaves["zeta"])
    for _ in range(13):
        expected = mul(expected, k0)
    q0 = mul(leaves["beta"], leaves["J"])
    c1 = add(add(q0, leaves["F"], -1), leaves["alpha"], -1)
    expected = mul(expected, add(mul(leaves["w"], c1), mul(leaves["z"], q0), -1))
    need(top["polynomial"] == expected and degree(expected) == 157, "entire degree157 leader")
    need(len(cancellations) == 1 and cancellations[0]["gate"] == "N1"
         and cancellations[0]["apparent_degree"] == 22
         and cancellations[0]["actual_degree"] == 18, "exact main-norm cancellation")
    factors = ["N0", "N1", "Na", "Nk", "Nt", "scaled_Ns"]
    factor_degrees = {name: degree(top[name]) for name in factors}
    need(list(factor_degrees.values()) == [22, 18, 62, 7, 2, 46], "exact factor degrees")
    distinguished = monomial({"beta": 92, "J": 92, "h": 1, "gamma": 1,
                              "i": 4, "eta": 13, "w": 13, "s": 26,
                              "T": 2, "f": 4, "z": 1}, 8)
    need(all(expected.get(m) == c for m, c in distinguished.items()), "nonzero specialized leading coefficient")

    negative_controls = []
    for name, override in [
        ("omit_denominator", {"U": leaves["MF"]}),
        ("wrong_W_sign", {"W": add(leaves["MC"], leaves["MF"])}),
        ("unwanted_W_denominator", {"W": mul(leaves["W"], monomial({"beta": -1}))}),
        ("unlicensed_four_gate_tail", {"W": {m: -c for m, c in leaves["beta"].items()}}),
    ]:
        need(exact_evaluator(new_rows, override)("R") != old_rank, name)
        negative_controls.append(name)
    bad_rows = deepcopy(new_rows)
    next(row for row in bad_rows if row[0] == "q2minus1")[3] = 2
    need(exact_evaluator(bad_rows)("R") != old_rank, "wrong q^2-1 constant")
    negative_controls.append("q2minus2")

    # Authenticate the complete existing tuple as bytes; neither import
    # the native compiler nor materialize a huge rational numerator here.
    binding = parent["coefficient_binding"]
    certificate_path = (PARENT / binding["certificate"]).resolve()
    certificate_raw = certificate_path.read_bytes()
    need(sha256(certificate_raw).hexdigest() == binding["certificate_sha256"],
         "whole complemented47 controller certificate")
    raw_total = 0
    coefficient_files = {}
    values = {}
    for port in ports:
        item = binding["ports"][port]
        path = PARENT / "coefficients" / item["file"]
        packed = path.read_bytes()
        raw = gzip.decompress(packed)
        need(sha256(packed).hexdigest() == item["gzip_sha256"], "compressed whole port hash")
        need(sha256(raw).hexdigest() == item["raw_sha256"], "raw whole port hash")
        raw_total += len(raw)
        need(len(raw) == item["raw_bytes"], "individual raw byte count")
        values[port] = int.from_bytes(raw, "big")
        need(values[port].bit_length() == item["bits"], "whole integer bit count")
        coefficient_files[port] = {"path": str(path.relative_to(ROOT)), **digest(raw)}
    need(raw_total == 207214 == binding["raw_bytes"], "all whole raw coefficient bytes")
    need(values["beta"] < values["MF"] < 2 * values["beta"], "1<U<2: sole rational leaf nonintegral")
    native_mf = values["MF"] - values["beta"]
    mask_populations = {"MC": values["MC"].bit_count(), "MF_native": native_mf.bit_count()}
    need(mask_populations == {"MC": 412947, "MF_native": 982}, "whole native mask populations")
    need(sum(mask_populations.values()) == 47 * 8807 and values["MC"] != native_mf,
         "odd-width obstruction to W=-beta")

    packet = {
        "name": "same_complemented47_integer_polynomial_single_rational65_evaluator",
        "metric": "Each binary +,-,* costs one; fixed rational leaves are free. This is not an integer-leaf65 record.",
        "witness_domain": "strictly positive integers",
        "witnesses": witnesses,
        "fixed_runtime_leaves": ["beta", "K0", "U", "W"],
        "derived_rational_leaves": {
            "U": {"numerator": "MF", "denominator": "beta"},
        },
        "derived_integer_leaves": {"W": "MC-MF"},
        "integer_source_ports": ports,
        "coefficient_binding_base": "../../candidates/one-page-complemented47-independent",
        "coefficient_binding": binding,
        "parent_snapshot": {"path": "source/parent66.json", **digest(parent_raw)},
        "source": new_rows,
        "output": "polynomial", "operations": 65, "operation_counts": new_counts,
        "exact_degree": 157,
        "proof": "README.md",
    }
    evidence = {
        "schema": "exact_single_rational_rank65_audit_v1",
        "old_counts": old_counts, "new_counts": new_counts,
        "rank_laurent_terms": len(new_rank), "rank_has_no_negative_exponents": True,
        "sole_noninteger_runtime_gate": "shifted_gap",
        "sole_noninteger_fixed_leaf": "U=MF/beta",
        "rank_product_and_rank_linear_have_integral_coefficients": True,
        "native_mask_populations": mask_populations,
        "W_equals_minus_beta": False,
        "universal_same_integer_polynomial": True,
        "all_65_gates_and_15_witnesses_and_4_runtime_leaves_live": True,
        "all_4_coherent_integer_ports_bound": True,
        "complete_output_leading_form_terms": len(expected),
        "exact_degree": 157, "factor_degrees": factor_degrees,
        "cancellations": cancellations,
        "nonzero_leading_coefficient": "8*beta^92 on J^92*h*gamma*i^4*eta^13*w^13*s^26*T^2*f^4*z",
        "negative_controls": negative_controls,
        "raw_coefficient_bytes": raw_total,
        "coefficient_files": coefficient_files,
        "source_inputs": {
            "source/parent66.json": digest(parent_raw),
            str(certificate_path.relative_to(ROOT)): digest(certificate_raw),
        },
        "limits": "Exact algebra/census/degree and existing tuple byte authentication; no new native calibration, formal-kernel proof, integer-leaf record, or global minimality theorem.",
    }
    for filename, data in [("polynomial.json", packet), ("AUDIT.json", evidence)]:
        path = HERE / filename
        raw = encoded(data)
        if args.write:
            path.write_bytes(raw)
        else:
            need(path.read_bytes() == raw, "deterministic output " + filename)
    print(json.dumps({"operations": 65, "metric": "rational leaves", "exact_degree": 157,
                      "same_integer_polynomial": True, "negative_controls": len(negative_controls)}))


if __name__ == "__main__":
    main()
