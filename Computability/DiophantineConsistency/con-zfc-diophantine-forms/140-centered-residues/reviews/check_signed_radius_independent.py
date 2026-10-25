#!/usr/bin/env python3
"""Independent exact audit of signed remainder-radius transformations.

No producer, projection routine, or vendored verifier is imported.
Unbounded number theory is established in the accompanying written review.
"""
from __future__ import annotations
from collections import defaultdict
import argparse
import hashlib
import json
from pathlib import Path

RELEASE_PARENT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = (RELEASE_PARENT / "arithmetic"
                if (RELEASE_PARENT / "arithmetic").is_dir()
                else RELEASE_PARENT / "direct_proto")
RELEASE_PROFILES = ("audit261", "signed259", "signed258")
WORK_PROFILES = ("signed_radius", "signed_odd_radius", "signed_weighted_odd_radius")


def need(value, message):
    if not value:
        raise ValueError(message)


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(obj):
    return hashlib.sha256(canon(obj)).hexdigest()


def read(path):
    return json.loads(path.read_text())


def normalize(terms):
    p = defaultdict(int)
    for coeff, mon in terms:
        need(type(coeff) is int, "Nonintegral coefficient")
        need(all(type(i) is int and i >= 0 for i in mon), "Bad coordinate")
        p[tuple(sorted(mon))] += coeff
    return {m: c for m, c in p.items() if c}


def add(*polys):
    result = defaultdict(int)
    for p in polys:
        for m, c in p.items():
            result[m] += c
    return {m: c for m, c in result.items() if c}


def scale(p, c):
    return {m: c*v for m, v in p.items() if c*v}


def multiply(p, q):
    result = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            result[tuple(sorted(m+n))] += a*b
    return {m: c for m, c in result.items() if c}


def variable(i):
    return {(i,): 1}


def constant(c):
    return {(): c} if c else {}


def substitute(p, replacements):
    result = {}
    for mon, coeff in p.items():
        term = constant(coeff)
        for i in mon:
            term = multiply(term, replacements.get(i, variable(i)))
        result = add(result, term)
    return result


def degree(p):
    return max(map(len, p), default=0)


def audit_mutation(source, metadata, raw, cert):
    need(sha(source) == cert["source_sha256"], "Input hash mismatch")
    need(sha(raw) == cert["target_sha256"], "Raw output hash mismatch")
    rows = source["residuals"]
    guards = {tuple(g["pair"]): g for g in metadata["guards"]
              if g["kind"] == "postsemantic_interval"}
    need(len(guards) == 11, "Expected eleven inherited intervals")
    need({(r["remainder"], r["slack"]) for r in cert["records"]} == set(guards),
         "Omitted or duplicated interval")
    removed_rows, removed_vars, d_by_r = set(), set(), {}
    for rec in cert["records"]:
        r, s, d = rec["remainder"], rec["slack"], rec["denominator"]
        aux = rec["auxiliary"]
        need(aux == guards[r,s]["auxiliary"], "Changed inherited guard witnesses")
        expected_bound = add(variable(d), scale(variable(r), -1), scale(variable(s), -1), constant(-1))
        expected_guard = add(multiply(variable(r), variable(s)),
                             *(scale(multiply(variable(a), variable(a)), -1) for a in aux),
                             scale(variable(aux[2]), -1))
        need(normalize(rows[rec["bound_row"]]["terms"]) == expected_bound, "Wrong old interval")
        need(normalize(rows[rec["guard_row"]]["terms"]) == expected_guard, "Wrong old product sign")
        need(rows[rec["bound_row"]]["label"] == rec["label"], "Interval label mismatch")
        removed_rows.update((rec["bound_row"], rec["guard_row"]))
        removed_vars.update((s, *aux))
        d_by_r[r] = d
    odd = cert.get("odd_square")
    if odd:
        o, q, aux = odd["old_slack"], odd["q"], odd["old_auxiliary"]
        g = next(g for g in metadata["guards"] if g["kind"] == "front_nonnegative" and g["coordinate"] == o)
        need(aux == g["auxiliary"], "Wrong output guard auxiliaries")
        expected_guard = add(variable(o), *(scale(multiply(variable(a), variable(a)), -1) for a in aux), scale(variable(aux[2]), -1))
        need(normalize(rows[odd["old_guard_row"]]["terms"]) == expected_guard, "Wrong output sign row")
        bound = normalize(rows[odd["old_bound_row"]]["terms"])
        need(rows[odd["old_bound_row"]]["label"] == "choose0.digit_bound", "Wrong output bound")
        need(bound.get((q,)) == 1 and bound.get((o,)) == -1 and bound.get(()) == -1,
             "Wrong output-bound shape")
        need(len(bound) == 4 and sum(c == -1 and len(m) == 1 for m,c in bound.items()) == 2,
             "Output bound is not q-B-o-1")
        removed_rows.update((odd["old_bound_row"], odd["old_guard_row"]))
        removed_vars.update((o, *aux))
    for i in removed_vars:
        actual_occurrences = {j for j, r in enumerate(rows) if any(i in mon for c, mon in r["terms"])}
        need(actual_occurrences <= removed_rows, "A deleted private coordinate has another use")
    live = sorted(set(range(len(source["variables"]))) - removed_vars)
    kept_rows = sorted(set(range(len(rows))) - removed_rows)
    need(live == cert["retained_source_variables"] and kept_rows == cert["retained_source_rows"], "Retention census mismatch")
    need(sorted(removed_vars) == cert["removed_variables"] and sorted(removed_rows) == cert["removed_rows"], "Deletion census mismatch")
    ren = {old: new for new, old in enumerate(live)}
    expected = {}
    for new, old in enumerate(kept_rows):
        expected[new] = (rows[old]["label"], {tuple(ren[i] for i in m): c for m,c in normalize(rows[old]["terms"]).items()})
    need(raw["variables"][:len(live)] == [source["variables"][i] for i in live], "Retained variables changed")
    new_variables = set()
    if odd:
        z = odd["new_root"]
        expected[odd["new_row"]] = ("radix.odd_square", add(variable(ren[q]), scale(multiply(variable(z), variable(z)), -4), scale(variable(z), -4), constant(-1)))
        new_variables.add(z)
    weighted = cert.get("weighted")
    if weighted:
        lo, hi = weighted["lower_power_call"], weighted["upper_power_call"]
        calls = metadata["square_budget"]["power_calls"]
        need(lo in calls and hi in calls, "Weighted denominator is not an inherited power")
        need(lo["base"] == hi["base"] == [[1, [weighted["q"]]]], "Different weighted radices")
        need(lo["output"] == [[1, [weighted["lower_denominator"]]]] and hi["output"] == [[1, [weighted["upper_denominator"]]]], "Different denominator outputs")
        need(add(normalize(hi["exponent"]), scale(normalize(lo["exponent"]), -1)) == constant(1), "Denominators are not consecutive powers")
    seen_remainders = []
    for j, cap in enumerate(cert["caps"]):
        d = cap["denominator_source"]
        product_by_r = {p["source_remainder"]: p for p in cap.get("products", [])}
        residues = []
        for r in cap["remainder_sources"]:
            seen_remainders.append(r)
            if r in product_by_r:
                p = product_by_r[r]
                need(weighted and p["source_weight"] == weighted["q"] and d_by_r[r] == weighted["lower_denominator"] and d == weighted["upper_denominator"], "Unlicensed radius scaling")
                v = p["variable"]
                expected[p["row"]] = ("radius.weighted_product."+str(r), add(variable(v), scale(multiply(variable(ren[p["source_weight"]]), variable(ren[r])), -1)))
                new_variables.add(v)
                residues.append(v)
            else:
                need(d_by_r[r] == d, "Mixed unscaled denominators")
                residues.append(ren[r])
        need(residues == cap.get("residue_coordinates", residues), "Scaled residual census mismatch")
        need(len(residues) <= 7, "Radius completeness bound exceeded")
        aux = cap["auxiliary"]
        need(len(aux) == 3 and not new_variables.intersection(aux), "Reused radius auxiliaries")
        new_variables.update(aux)
        polynomial = add(multiply(variable(ren[d]), variable(ren[d])), constant(-1),
                         *(scale(multiply(variable(v), variable(v)), -4) for v in residues),
                         *(scale(multiply(variable(a), variable(a)), -1) for a in aux),
                         scale(variable(aux[2]), -1))
        expected[cap["row"]] = (f"centered_remainder_radius.{j}", polynomial)
    need(sorted(seen_remainders) == sorted(d_by_r), "Remainders not partitioned exactly once")
    need(new_variables == set(range(len(live), len(raw["variables"]))), "Undeclared extra coordinates")
    need(set(expected) == set(range(len(raw["residuals"]))), "Extra or missing rows")
    for i, r in enumerate(raw["residuals"]):
        label, polynomial = expected[i]
        need(label == r["label"] and polynomial == normalize(r["terms"]), f"Raw row {i} changed")
    return len(removed_rows), len(removed_vars)


def audit_projection(raw, dst, cert):
    need(sha(raw) == cert["input_sha256"] and sha(dst) == cert["output_sha256"], "Projection hash mismatch")
    rows = {i: normalize(r["terms"]) for i,r in enumerate(raw["residuals"])}
    deleted = set()
    for step in cert["steps"]:
        v, row = step["variable"], step["row_id"]
        restoration = normalize(step["restoration"])
        need(v not in deleted and row in rows, "Repeated elimination")
        need(degree(restoration) <= 2 and not any(v in m or deleted.intersection(m) for m in restoration), "Invalid restoration dependency")
        identity = add(variable(v), scale(restoration, -1))
        need(rows[row] == identity or rows[row] == scale(identity, -1), "Nonmonic elimination")
        del rows[row]
        for j in list(rows):
            rows[j] = substitute(rows[j], {v: restoration})
            need(degree(rows[j]) <= 2, "Elimination increased degree")
            if not rows[j]:
                del rows[j]
        deleted.add(v)
    live = sorted({v for p in rows.values() for m in p for v in m})
    keep = sorted(rows)
    need(live == cert["retained_original_variables"] and keep == cert["retained_original_rows"], "Final projection census")
    need(sorted(set(range(len(raw["variables"]))) - set(live) - deleted) == cert["unconstrained_removed"], "Free coordinates census")
    ren = {v: j for j,v in enumerate(live)}
    need(dst["variables"] == [raw["variables"][v] for v in live], "Projected variable order")
    need(len(dst["residuals"]) == len(keep), "Projected row count")
    for row, j in zip(dst["residuals"], keep):
        expected = {tuple(ren[v] for v in m): c for m,c in rows[j].items()}
        need(row["label"] == raw["residuals"][j]["label"] and normalize(row["terms"]) == expected, "Projected polynomial mismatch")
    return len(cert["steps"])


def audit_translation(src, dst, cert):
    need(cert["convention"] == "old=new+shift", "Unknown translation convention")
    need(sha(src) == cert["input_sha256"] and sha(dst) == cert["output_sha256"], "Translation hash mismatch")
    shifts = dict(cert["shifts"])
    need(len(shifts) == len(cert["shifts"]) and all(type(i) is int and type(d) is int for i,d in shifts.items()), "Invalid translation")
    need(src["variables"] == dst["variables"] and len(src["residuals"]) == len(dst["residuals"]), "Translation changed census")
    replacements = {i: add(variable(i), constant(d)) for i,d in shifts.items()}
    for a,b in zip(src["residuals"], dst["residuals"]):
        need(a["label"] == b["label"] and substitute(normalize(a["terms"]), replacements) == normalize(b["terms"]), "Translated polynomial mismatch")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="Arithmetic directory containing signed_source and audit261/signed259/signed258; defaults to ../arithmetic in a release, otherwise ../direct_proto. Original work-profile names are also supported.")
    root = parser.parse_args().root.resolve()
    source = read(root/"signed_source/factored_source.json")
    metadata = read(root/"signed_source/transform_certificate.json")
    receipts = []
    profiles = RELEASE_PROFILES if (root/RELEASE_PROFILES[0]).is_dir() else WORK_PROFILES
    for name in profiles:
        folder = root/name
        raw, projected, final = [read(folder/f) for f in ("raw_equation.json", "projected.json", "equation.json")]
        mutation = audit_mutation(source, metadata, raw, read(folder/"radius_certificate.json"))
        steps = audit_projection(raw, projected, read(folder/"projection.json"))
        audit_translation(projected, final, read(folder/"translation.json"))
        polynomial, used = {}, set()
        for row in final["residuals"]:
            r = normalize(row["terms"])
            need(degree(r) <= 2, "Nonquadratic final row")
            used.update(v for m in r for v in m)
            polynomial = add(polynomial, multiply(r,r))
        need(used == set(range(len(final["variables"]))), "Unused or illegal final coordinate")
        need(polynomial == normalize(read(folder/"expanded_polynomial.json")["terms"]), "Collected coefficient mismatch")
        metrics = dict(variables=len(final["variables"]), rows=len(final["residuals"]), degree=degree(polynomial), monomials=len(polynomial), height=max(map(abs, polynomial.values())), row_height=max(abs(c) for row in final["residuals"] for c,m in row["terms"]))
        need(metrics == read(folder/"metrics.json"), "Recorded metric mismatch")
        receipts.append(dict(variant=name, equation_file_sha256=hashlib.sha256((folder/"equation.json").read_bytes()).hexdigest(), new_raw_rows=len(raw["residuals"]), new_raw_variables=len(raw["variables"]), removed_rows=mutation[0], removed_variables=mutation[1], monic_projection_steps=steps, metrics=metrics))
    print(json.dumps(dict(status="passed", source_file_sha256=hashlib.sha256((root/"signed_source/factored_source.json").read_bytes()).hexdigest(), checks=receipts, scope="Complete exact mutation, projection, translation and collected coefficients; no producer imports. Unbounded arithmetic needs the written proof."), indent=2))


if __name__ == "__main__":
    main()
