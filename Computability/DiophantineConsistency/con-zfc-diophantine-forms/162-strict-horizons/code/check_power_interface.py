#!/usr/bin/env python3
"""Independent exact audit of the 17-request strict-horizon power interface.

No construction or projection module is imported.  The request table, frame,
signed cap, range denominators, and semantic-anchor assembly are specified
independently below.  This finite audit checks the raw source identities;
unbounded Pell/CRT reasoning, C222 calibration, and transport through the
projection certificates remain separate proof obligations.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path


def add(*polys):
    result = defaultdict(int)
    for poly in polys:
        for mon, coefficient in poly.items():
            result[mon] += coefficient
    return {mon: c for mon, c in result.items() if c}


def scale(poly, coefficient):
    return {mon: c * coefficient for mon, c in poly.items() if c * coefficient}


def mul(left, right):
    result = defaultdict(int)
    for a, c in left.items():
        for b, d in right.items():
            result[tuple(sorted(a + b))] += c * d
    return {mon: c for mon, c in result.items() if c}


def square(poly):
    return mul(poly, poly)


def constant(c):
    return {(): c} if c else {}


def variable(i):
    return {(i,): 1}


def normalize(terms):
    return add(*[{tuple(sorted(mon)): coefficient} for coefficient, mon in terms])


def equal(actual, expected, label):
    difference = add(actual, scale(expected, -1))
    if difference:
        raise ValueError(f"{label}: polynomial mismatch {difference}")


def audit_object(source):
    variables = source["variables"]
    names = {v["name"]: i for i, v in enumerate(variables)}
    if len(names) != len(variables):
        raise ValueError("duplicate coordinate name")
    labels = defaultdict(list)
    live = set()
    for residual in source["residuals"]:
        for coefficient, mon in residual["terms"]:
            if not isinstance(coefficient, int) or any(not isinstance(i, int) or not 0 <= i < len(variables) for i in mon):
                raise ValueError("malformed polynomial term")
            if len(mon) > 2:
                raise ValueError("raw residual is not quadratic")
            if coefficient:
                live.update(mon)
        labels[residual["label"]].append(normalize(residual["terms"]))

    def row(label):
        if len(labels[label]) != 1:
            raise ValueError(f"nonunique or missing row {label}: {len(labels[label])}")
        return labels[label][0]

    def v(name):
        return variable(names[name])

    t = add(v("t0"), constant(16))
    x, y = v("x"), v("y")
    f, radius = v("crt.growth_majorant_F"), v("mul.1")
    b, q, a, w = v("choose0.output"), v("pow2.output"), v("shared.A"), v("shared.W")
    base, bh = v("growth.power_base"), v("self_radix.BH")
    representative_names = ["crt.encoded." + name for name in ("a", "b", "c", "d", "S", "Sp", "u", "vq")] + ["crt.encoded_index_minus_one"]
    representatives = [add(v(name), constant(1)) for name in representative_names]
    anchor = add(v("add.380"), constant(1))
    output = lambda call: f if call == 0 else v(f"pow{call}.output")

    obsolete = ["growth.power_U", "pow6.output", "index_addition.D", "pow6.quotient", "remainder_budget.ratio1", "mul.541", "mul.543", "mul.544", "mul.547", "mul.549", "mul.550"]
    for name in obsolete:
        if names.get(name) in live:
            raise ValueError(f"obsolete coordinate remains live: {name}")
    for label in ("growth.majorant_definition", "pow6.power_congruence", "index_addition.D_definition", "remainder_budget.ratio1", "radix.odd_square"):
        if labels[label]:
            raise ValueError(f"obsolete residual remains: {label}")

    front = {
        "growth.base_definition": add(base, scale(t, -1)),
        "cofinal.horizon": add(v("t0"), scale(square(v("cofinal.horizon_root")), -1)),
        "crt.linear_radius": add(radius, scale(f, -1)),
        "self_radix.base_definition": add(bh, scale(mul(b, add(constant(2), *representatives)), -1)),
        "radix.affine_class": add(q, scale(v("radix.odd_square_root_half"), -4), constant(-1)),
        "beta.odd_square_multiplier": add(v("beta.odd_square_multiplier"), scale(square(add(scale(v("beta.odd_square_root_half"), 2), constant(1))), -1)),
        "bootstrap.beta_base_square_product": add(y, scale(mul(f, v("beta.odd_square_multiplier")), -1)),
    }
    for label, expected in front.items():
        equal(row(label), expected, label)

    # (call number, base, index, output, principal pair).  The former call 6,
    # q^(t+1), is absent.  Call 4, q^t, now supplies all strict label ranges.
    requests = [
        (0, base, t, output(0), "index0"),
        (1, b, x, output(1), "index12"),
        (2, bh, x, output(2), "index12"),
        (3, add(q, constant(1)), add(radius, t), output(3), "index2"),
        (4, q, t, output(4), "index0"),
        (5, add(q, constant(1)), representatives[0], output(5), "index3"),
        (7, add(q, constant(1)), representatives[1], output(7), "index5"),
        (8, add(q, constant(1)), representatives[2], output(8), "index6"),
        (9, add(q, constant(1)), representatives[3], output(9), "index7"),
        (10, add(q, constant(1)), representatives[4], output(10), "index8"),
        (11, q, add(y, constant(1)), output(11), "index9"),
        (12, add(q, constant(1)), representatives[5], output(12), "index10"),
        (13, add(q, constant(1)), representatives[6], output(13), "index11"),
        (14, q, x, output(14), "index12"),
        (15, add(q, constant(1)), representatives[7], output(15), "index13"),
        (16, add(q, constant(1)), representatives[8], output(16), "index14"),
        (17, add(q, constant(1)), anchor, output(17), "index15"),
    ]
    actual_calls = {int(match.group(1)) for label in labels if labels[label] and (match := re.fullmatch(r"pow(\d+)\.power_congruence", label))}
    if actual_calls != {r[0] for r in requests}:
        raise ValueError(f"incorrect power-call set: {sorted(actual_calls)}")

    # The equality d=t is already checked.  Canonicalizing ONLY that scalar
    # identity makes the duplicate d^2 redundant in the square frame.  R and
    # F remain separate source atoms, as in the actual released frame.
    atoms = {}
    for _, n, k, m, _ in requests:
        for poly in (n, k, m):
            canonical = t if poly == base else poly
            atoms[tuple(sorted(canonical.items()))] = canonical
    equal(row("shared.frame_definition"), add(w, constant(-2), *[scale(square(p), -1) for p in atoms.values()]), "complete deduplicated square frame")

    # Extract only elementary monic multiplication definitions.  Their
    # right-hand sides are independently substituted in each identity below.
    gate_definitions = {}
    for poly in labels["multiplication"]:
        candidates = [mon[0] for mon, c in poly.items() if len(mon) == 1 and c == 1 and variables[mon[0]]["kind"] == "gate"]
        if len(candidates) != 1:
            raise ValueError("ambiguous multiplication definition")
        i = candidates[0]
        if i in gate_definitions or any(i in mon for mon in poly if mon != (i,)):
            raise ValueError("nonfunctional multiplication definition")
        gate_definitions[i] = scale(add(poly, scale(variable(i), -1)), -1)
    stop = {i for _, n, k, m, _ in requests for p in (n, k, m) for mon in p for i in mon}
    stop.update((names["shared.A"], names["shared.W"]))

    def expand(poly, stack=()):
        result = {}
        for mon, coefficient in poly.items():
            product = constant(coefficient)
            for i in mon:
                if i in gate_definitions and i not in stop:
                    if i in stack:
                        raise ValueError("cyclic multiplication definitions")
                    factor = expand(gate_definitions[i], stack + (i,))
                else:
                    factor = variable(i)
                product = mul(product, factor)
            result = add(result, product)
        return result

    principal = {}
    for _, _, exponent, _, prefix in requests:
        if prefix in principal:
            equal(principal[prefix], exponent, "shared principal index")
        principal[prefix] = exponent
    actual_principal = {label[:-6] for label in labels if labels[label] and re.fullmatch(r"index\d+\.norm1", label)}
    if actual_principal != set(principal) or len(principal) != 14:
        raise ValueError("incorrect principal-pair set")
    pool = []
    for prefix, exponent in principal.items():
        xp, yp = v(prefix + ".X"), v(prefix + ".Y")
        equal(expand(row(prefix + ".norm1")), add(square(xp), square(yp), scale(mul(square(a), square(yp)), -1), constant(-1)), prefix + " Pell norm")
        pool.extend((square(add(xp, constant(-1))), square(add(yp, scale(exponent, -1)))))
    pool.append(scale(mul(add(a, constant(-1)), v("cap.pooled_quotient")), -1))
    equal(row("cap.pooled_index_residue"), add(*pool), "all fourteen paired signed indices")

    bases = [base, b, bh, add(q, constant(1)), q]
    for i, n in enumerate(bases):
        equal(expand(row(f"base{i}.T_definition")), add(scale(mul(a, n), 2), scale(square(n), -1), constant(-1), scale(v(f"base{i}.T"), -1)), f"base{i} modulus")
    call_base = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 3, 7: 3, 8: 3, 9: 3, 10: 3, 11: 4, 12: 3, 13: 3, 14: 4, 15: 3, 16: 3, 17: 3}
    for call, n, _, m, prefix in requests:
        xp, yp = v(prefix + ".X"), v(prefix + ".Y")
        expected = add(xp, scale(mul(a, yp), -1), mul(n, yp), scale(m, -1), scale(mul(v(f"base{call_base[call]}.T"), v(f"pow{call}.quotient")), -1))
        equal(expand(row(f"pow{call}.power_congruence")), expected, f"power request {call}")

    last_y = mul(w, add(constant(1), scale(v("shared.Zminus1"), 2)))
    equal(expand(row("shared.last_norm")), add(square(a), square(last_y), scale(square(mul(add(w, constant(1)), last_y)), -1), constant(-1)), "signed shared-frame norm")

    # Reuse the actual derived-label pair for the one-row signed cap.
    cap_h, cap_j = v("cap.H"), v("cap.J")
    cap_s, cap_r, cap_b = v("cap.S"), v("cap.R"), v("cap.B")
    anchor_x, anchor_y = v("index15.X"), v("index15.Y")
    cap_gates = {
        "cap.common_Ay": mul(a, cap_j),
        "cap.BR": mul(cap_b, cap_r),
        "cap.Y2": square(anchor_y),
    }
    for name, expected in cap_gates.items():
        equal(row(name), add(v(name), scale(expected, -1)), name)
        gate_definitions[names[name]] = expected
    cap_rows = {
        "cap.common_norm": add(square(cap_h), square(cap_j), scale(square(mul(a, cap_j)), -1), constant(-1)),
        "cap.comparison_norm": add(square(cap_s), square(cap_r), scale(square(mul(cap_b, cap_r)), -1), constant(-1)),
        "cap.common_multiple": add(cap_j, scale(mul(square(anchor_y), add(constant(1), scale(v("cap.e"), 2))), -1)),
        "cap.comparison_constructor": add(cap_b, constant(-1), scale(mul(cap_j, add(constant(1), scale(v("cap.d"), 2))), -4)),
        "cap.comparison_modulus": add(cap_b, scale(a, -1), scale(mul(cap_h, v("cap.f")), -1)),
        "cap.abscissa_residue": add(cap_s, scale(anchor_x, -1), scale(mul(cap_h, v("cap.g")), -1)),
        "cap.index_residue": add(cap_r, scale(anchor, -1), scale(mul(anchor_y, v("cap.h")), -4)),
    }
    for label, expected in cap_rows.items():
        equal(expand(row(label)), expected, label)
    expected_cap_labels = set(cap_gates) | set(cap_rows) | {"cap.pooled_index_residue"}
    if {label for label in labels if labels[label] and label.startswith("cap.")} != expected_cap_labels:
        raise ValueError("unexpected or missing signed-cap residual")
    guard3 = add(square(anchor_y), scale(square(anchor), -1), constant(-1), *[scale(square(v(prefix + ".Y")), -1) for prefix in principal if prefix != "index15"], scale(square(v("new_guard3.a")), -1), scale(square(v("new_guard3.b")), -1), scale(mul(v("new_guard3.c"), add(v("new_guard3.c"), constant(1))), -1))
    equal(row("domain_guard.3"), guard3, "anchor dominance over every other principal ordinate")

    # Literal affine assembly of the inherited constructor-label sum.  This
    # checks its attachment to the anchor; C222 constructor calibration is
    # still supplied by the inherited proof, not inferred from this check.
    anchor_assembly = {
        "add.370": add(constant(12), scale(v("add.61"), 2), scale(v("add.71"), 4), scale(v("mul.86"), 2), scale(v("add.101"), 2)),
        "add.372": add(constant(12), scale(v("add.112"), 4), scale(v("mul.123"), 2), scale(v("add.142"), 2), v("add.370")),
        "add.375": add(scale(v("add.156"), 4), scale(v("mul.159"), 2), scale(v("add.181"), 2), scale(v("add.199"), 2), v("add.372")),
        "add.377": add(constant(1), v("crt.encoded.a"), scale(v("add.308"), 4), scale(v("mul.311"), 2), v("add.375")),
        "add.379": add(constant(3), scale(v("crt.encoded.a"), 2), v("crt.encoded.b"), scale(v("mul.40"), 2), v("add.377")),
        "add.380": add(constant(20), scale(v("crt.encoded.a"), 6), scale(v("crt.encoded.b"), 8), scale(v("mul.40"), 2), v("add.379")),
    }
    for name, expected in anchor_assembly.items():
        identity = add(v(name), scale(expected, -1))
        if sum(poly == identity for poly in labels["addition"]) != 1:
            raise ValueError(f"semantic-anchor assembly changed: {name}")

    # Every digit remainder is normalized by the same D=q^x.  There are now
    # only two denominator ratios, D/q^t and D/q^(y+1).
    common_d, n = output(14), output(1)
    ratio0, ratio2 = v("remainder_budget.ratio0"), v("remainder_budget.ratio2")
    equal(row("remainder_budget.ratio0"), add(common_d, scale(mul(output(4), ratio0), -1)), "common D/q^t ratio")
    equal(row("remainder_budget.ratio2"), add(common_d, scale(mul(output(11), ratio2), -1)), "common D/q^(y+1) ratio")
    equal(expand(row("choose0.digit")), add(mul(output(3), ratio0), scale(v("normalized.choose0.remainder"), -1), scale(mul(common_d, add(b, mul(q, v("choose0.high")))), -1)), "authenticated binomial B digit")
    range_calls = [5, 7, 8, 9, 10, 12, 13, 15, 16, 17]
    range_names = ["a", "b", "c", "d", "S", "Sp", "u", "vq", "index", "derived_label_sum"]
    remainders = [v("normalized.choose0.remainder")]
    for i, (call, name) in enumerate(zip(range_calls, range_names)):
        ratio = ratio0 if i in (0, 1, 2, 3, 8, 9) else ratio2 if i in (4, 5) else constant(1)
        remainder = v(f"normalized.range{i}.remainder")
        remainders.append(remainder)
        expected = add(mul(output(call), ratio), scale(remainder, -1), scale(mul(mul(n, common_d), v(f"range{i}.quotient")), -1))
        equal(expand(row(f"crt.range.{name}.quotient_multiple")), expected, f"range {name}: denominator and common modulus")
    guard4 = add(square(common_d), *[scale(square(r), -4) for r in remainders], constant(-1), scale(square(v("new_guard4.a")), -1), scale(square(v("new_guard4.b")), -1), scale(mul(v("new_guard4.c"), add(v("new_guard4.c"), constant(1))), -1))
    equal(row("domain_guard.4"), guard4, "all eleven normalized remainders share the strict budget")

    return {
        "status": "passed", "requests_checked": len(requests),
        "call_numbers": [r[0] for r in requests],
        "distinct_frame_atoms": len(atoms), "principal_pairs_checked": len(principal),
        "base_moduli_checked": len(bases), "front_bootstrap_rows_checked": len(front),
        "signed_cap_rows_checked": len(expected_cap_labels),
        "semantic_anchor_assembly_rows_checked": len(anchor_assembly),
        "strict_parameter_and_label_ranges_checked": 5,
        "ranges_using_q_to_t_denominator": 6,
        "total_range_rows_checked": 10, "normalized_remainders_checked": len(remainders),
        "obsolete_coordinates_confirmed_dead": obsolete,
        "derived_addition_pair_absent": True,
        "compiler_imports": False,
        "scope": "Exact raw-source polynomial identities; unbounded mathematical soundness, C222/ZFC calibration, and projection transport are separate obligations.",
    }


def controls(source):
    """Deliberate changes must be rejected by semantic-identity checks."""
    names = {v["name"]: i for i, v in enumerate(source["variables"])}

    def alter(label, term):
        def mutation(copy_source):
            targets = [r for r in copy_source["residuals"] if r["label"] == label]
            if len(targets) != 1:
                raise ValueError("bad corruption-control target")
            targets[0]["terms"].append(term)
        return mutation

    def range_alias(copy_source):
        target = next(r for r in copy_source["residuals"] if r["label"] == "crt.range.a.quotient_multiple")
        for _, mon in target["terms"]:
            for j, i in enumerate(mon):
                if i == names["remainder_budget.ratio0"]:
                    mon[j] = names["remainder_budget.ratio2"]

    def common_modulus(copy_source):
        target = next(r for r in copy_source["residuals"] if r["label"] == "multiplication" and [1, [names["mul.430"]]] in r["terms"])
        target["terms"].append([1, [names["pow1.output"], names["pow14.output"]]])

    def squared_radius(copy_source):
        target = next(r for r in copy_source["residuals"] if r["label"] == "crt.linear_radius")
        target["terms"].extend([[1, [names["crt.growth_majorant_F"]]], [-1, [names["crt.growth_majorant_F"], names["crt.growth_majorant_F"]]]])

    mutations = {
        "omit_one_radix_square_from_frame": alter("shared.frame_definition", [1, [names["pow2.output"], names["pow2.output"]]]),
        "restore_duplicate_growth_base_square": alter("shared.frame_definition", [-1, [names["growth.power_base"], names["growth.power_base"]]]),
        "wrong_live_range_ratio": range_alias,
        "wrong_common_range_modulus": common_modulus,
        "wrong_principal_pell_norm": alter("index3.norm1", [1, []]),
        "omit_one_principal_from_pooled_index": alter("cap.pooled_index_residue", [-1, [names["index12.Y"], names["index12.Y"]]]),
        "shift_cap_anchor_index": alter("cap.index_residue", [1, []]),
        "omit_one_ordinate_from_anchor_dominance": alter("domain_guard.3", [1, [names["index3.Y"], names["index3.Y"]]]),
        "revive_obsolete_q_to_t_plus_one": alter("shared.frame_definition", [1, [names["pow6.output"]]]),
        "weaken_affine_radix_class": alter("radix.affine_class", [2, [names["radix.odd_square_root_half"]]]),
        "restore_squared_radius": squared_radius,
        "shift_first_range_remainder": alter("crt.range.a.quotient_multiple", [1, []]),
    }
    results = {}
    for label, mutation in mutations.items():
        changed = copy.deepcopy(source)
        mutation(changed)
        try:
            audit_object(changed)
        except ValueError as error:
            results[label] = {"rejected": True, "reason": str(error)}
        else:
            raise ValueError(f"corruption control was incorrectly accepted: {label}")
    return results


def audit(path, run_controls=True):
    raw = path.read_bytes()
    source = json.loads(raw)
    report = audit_object(source)
    report["raw_source_sha256"] = hashlib.sha256(raw).hexdigest()
    if run_controls:
        report["corruption_controls"] = controls(source)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path,
                        default=Path(__file__).resolve().parent.parent / "direct/source/raw_source.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(audit(args.source), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
