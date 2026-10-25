#!/usr/bin/env python3
"""Independent literal review of the new signed digit-pool construction.

Uses only the standard library. Imports no producer or inherited algebra module.
It checks the new source boundary, exact recorded factorization patch, monic
projection, integral translations, and every collected SOS coefficient. The
semantic factorization theorem and pre-existing source calibration are inherited;
the new unbounded arithmetic argument is reviewed separately.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import copy
import hashlib
import json


def need(value, text):
    if not value:
        raise ValueError(text)


def read(path):
    return json.loads(path.read_text())


def digest(data):
    raw = (json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n").encode()
    return hashlib.sha256(raw).hexdigest()


def poly(terms):
    out = {}
    for c, m in terms:
        need(type(c) is int and c != 0, "coefficient must be a nonzero integer")
        need(all(type(i) is int and i >= 0 for i in m), "invalid coordinate")
        need(m == sorted(m), "noncanonical monomial")
        k = tuple(m)
        need(k not in out, "duplicate monomial")
        out[k] = c
    return out


def add(*values):
    out = defaultdict(int)
    for value in values:
        for m, c in value.items():
            out[m] += c
    return {m: c for m, c in out.items() if c}


def neg(value):
    return {m: -c for m, c in value.items()}


def mul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return {m: c for m, c in out.items() if c}


def subst(p, index, value):
    out = {}
    for monomial, coefficient in p.items():
        term = {(): coefficient}
        for v in monomial:
            term = mul(term, value if v == index else {(v,): 1})
        out = add(out, term)
    return out


def degree(p):
    return max(map(len, p), default=0)


def source_review(parent, metadata, source, certificate):
    need(certificate["parent_sha256"] == digest(parent), "parent hash")
    need(certificate["target_sha256"] == digest(source), "source hash")
    need(certificate["source_certificate_sha256"] == digest(metadata), "metadata hash")
    need(source["domain"] == parent["domain"] == "unrestricted integers", "wrong domain")
    names = {v["name"]: i for i, v in enumerate(parent["variables"])}
    q = names["pow2.output"]
    odd = certificate.get("odd_radix") is not None
    needed_guards = []
    for j, guard in enumerate(metadata["guards"]):
        remove = guard["kind"] == "postsemantic_interval"
        remove |= odd and guard["kind"] == "front_nonnegative" and guard["coordinate"] == names["choose0.oslack"]
        if remove:
            needed_guards.append((j, guard))
    labels = {"domain_guard." + str(j) for j, g in needed_guards}
    expected_removed = [r for r in parent["residuals"] if r["label"] in labels]
    need(len(expected_removed) == 11 + int(odd), "deletion census")
    need(expected_removed == certificate["removed_guard_rows"], "removed rows")
    expected_rows = [r for r in parent["residuals"] if r["label"] not in labels]
    need(source["residuals"][:len(expected_rows)] == expected_rows, "unrelated source row changed")
    n = len(parent["variables"])
    need(source["variables"][:n] == parent["variables"], "old coordinate changed")
    tail = source["residuals"][len(expected_rows):]
    by_label = {r["label"]: poly(r["terms"]) for r in tail}
    need(len(by_label) == len(tail), "duplicate new label")
    expected_tail = {}
    used_new = set()
    if odd:
        info = certificate["odd_radix"]
        z = info["root"]
        need(z >= n and info["radix"] == q, "odd-square ports")
        expected_tail["odd_radix.square"] = {(q,): 1, (z, z): -4, (z,): -4, (): -1}
        used_new.add(z)
    denominators = [names[s] for s in ["pow4.output", "pow6.output", "pow11.output", "pow14.output"]]
    remainders = [[names[s] for s in ["choose0.remainder", "range8.remainder"]],
                  [names["range" + str(i) + ".remainder"] for i in [0, 1, 2, 3, 9]],
                  [names["range" + str(i) + ".remainder"] for i in [4, 5]],
                  [names["range" + str(i) + ".remainder"] for i in [6, 7]]]
    ordinary_den = {r: d for d, rr in zip(denominators, remainders) for r in rr}
    for j, guard in needed_guards:
        if guard["kind"] != "postsemantic_interval":
            continue
        r, s = guard["pair"]
        need(r in ordinary_den, "unrecognized old interval")
        bound = {(ordinary_den[r],): 1, (r,): -1, (s,): -1, (): -1}
        need(any(poly(row["terms"]) in (bound, neg(bound)) for row in expected_rows), "old remainder bound absent")
        a, b, c = guard["auxiliary"]
        old = {tuple(sorted((r, s))): 1, (a, a): -1, (b, b): -1, (c, c): -1, (c,): -1}
        need(poly(parent["residuals"][guard["row"]]["terms"]) == old, "old guard not ternary product graph")
    scales = certificate["scaled_remainders"]
    if scales:
        need(len(scales) == 2, "scale census")
        for r, spec in zip(remainders[0], scales):
            z = spec["output"]
            need(spec["input"] == r and spec["factor"] == q and z >= n, "scale port")
            need(z not in used_new, "reused new coordinate")
            used_new.add(z)
            label = "digit_pool.scale." + parent["variables"][r]["name"]
            expected_tail[label] = {(z,): 1, tuple(sorted((q, r))): -1}
        remainders[1] += [s["output"] for s in scales]
        denominators, remainders = denominators[1:], remainders[1:]
    groups = certificate["groups"]
    need(len(groups) == len(denominators), "pool count")
    for d, rr, group in zip(denominators, remainders, groups):
        need(group["denominator"] == d and group["remainders"] == rr, "pool ports")
        aux = group["auxiliary"]
        need(len(set(aux)) == 3 and min(aux) >= n and not set(aux) & used_new, "pool auxiliary collision")
        used_new.update(aux)
        a, b, c = aux
        p = {(d, d): 1, (): -1, (a, a): -1, (b, b): -1, (c, c): -1, (c,): -1}
        for r in rr:
            p = add(p, {(r, r): -4})
        expected_tail["digit_pool." + group["tag"]] = p
    need(expected_tail == by_label, "new source rows differ from proved formulas")
    need(used_new == set(range(n, len(source["variables"]))), "unexpected new coordinate")
    dead = {a for j, g in needed_guards for a in g["auxiliary"]}
    need(dead == set(certificate["removed_private_auxiliaries"]), "old private coordinate census")
    need(not any(v in dead for row in source["residuals"] for m in poly(row["terms"]) for v in m), "removed auxiliary escaped")
    return {"old_product_guards": 11, "odd_square": odd, "new_pools": len(groups), "retained_rows": len(expected_rows)}


def patch_review(source, target, certificate):
    need(digest(source) == certificate["input_sha256"], "factor input hash")
    need(digest(target) == certificate["output_sha256"], "factor output hash")
    rows = copy.deepcopy(source["residuals"])
    seen = set()
    for change in certificate["changes"]:
        i = change["row"]
        need(i not in seen and rows[i]["terms"] == change["old"], "factor patch preimage")
        seen.add(i)
        rows[i]["terms"] = change["new"]
    deleted = set(certificate["deleted_rows"])
    need(len(deleted) == 2 and not deleted & seen, "factor deletion boundary")
    rows = [r for i, r in enumerate(rows) if i not in deleted]
    rows.append({"label": "factored.horn", "terms": certificate["new_row"]})
    need(rows == target["residuals"], "factor patch image")
    need(target["variables"][-1] == {"name": "factored.horn", "kind": "gate"}, "factor terminal coordinate")
    need(certificate["new_root"] == len(source["variables"]), "factor root index")
    return {"recorded_changes": len(seen), "deleted_rows": len(deleted)}


def projection_review(source, target, certificate):
    need(digest(source) == certificate["input_sha256"] and digest(target) == certificate["output_sha256"], "projection hashes")
    rows = {i: poly(r["terms"]) for i, r in enumerate(source["residuals"])}
    live = set(range(len(source["variables"])))
    for step in certificate["steps"]:
        i, v = step["row_id"], step["variable"]
        need(i in rows and v in live, "elimination repeats a coordinate or row")
        restoration = poly(step["restoration"])
        need(all(w in live and w != v for m in restoration for w in m), "restoration references dead/self coordinate")
        coefficient = rows[i].get((v,), 0)
        need(coefficient in (-1, 1), "nonmonic elimination")
        desired = add({(v,): coefficient}, {m: -coefficient*c for m, c in restoration.items()})
        need(rows[i] == desired, "restoration not exact row solution")
        del rows[i]
        for j in list(rows):
            rows[j] = subst(rows[j], v, restoration)
            need(degree(rows[j]) <= 2, "elimination raises residual degree")
            if not rows[j]:
                del rows[j]
        live.remove(v)
    occurrences = {v for p in rows.values() for m in p for v in m}
    need(sorted(live-occurrences) == certificate["unconstrained_removed"], "unconstrained removal")
    original_vars = sorted(occurrences)
    original_rows = sorted(rows)
    need(original_vars == certificate["retained_original_variables"] and original_rows == certificate["retained_original_rows"], "retained order")
    renaming = {v: i for i, v in enumerate(original_vars)}
    need(target["variables"] == [source["variables"][v] for v in original_vars], "projected variable names")
    need(len(target["residuals"]) == len(rows), "projected row count")
    for i, actual in zip(original_rows, target["residuals"]):
        p = {tuple(renaming[v] for v in m): c for m, c in rows[i].items()}
        need(poly(actual["terms"]) == p and actual["label"] == source["residuals"][i]["label"], "projected row mismatch")
    return {"monic_restorations": len(certificate["steps"]), "unconstrained_removed": len(live-occurrences)}


def translation_review(source, target, certificate):
    need(digest(source) == certificate["input_sha256"] and digest(target) == certificate["output_sha256"], "translation hashes")
    need(certificate["convention"] == "old=new+shift", "shift convention")
    need(source["variables"] == target["variables"], "translation coordinate names")
    need(len(source["residuals"]) == len(target["residuals"]), "translation row count")
    shifts = dict(certificate["shifts"])
    need(len(shifts) == len(certificate["shifts"]), "repeated shift")
    for row, result in zip(source["residuals"], target["residuals"]):
        p = poly(row["terms"])
        for v, d in shifts.items():
            need(type(d) is int and 0 <= v < len(source["variables"]), "invalid integer shift")
            p = subst(p, v, {(v,): 1, (): d} if d else {(v,): 1})
        need(p == poly(result["terms"]) and row["label"] == result["label"], "translation identity")
    return {"translated_coordinates": len(shifts)}


def expansion_review(equation, expansion):
    rows = [poly(r["terms"]) for r in equation["residuals"]]
    need(all(degree(r) <= 2 for r in rows), "nonquadratic row")
    p = add(*(mul(r, r) for r in rows))
    need(p == poly(expansion["terms"]), "collected coefficient mismatch")
    need(set(range(len(equation["variables"]))) == {v for m in p for v in m}, "dead final coordinate")
    need(degree(p) == 4, "degree is not exactly four")
    return {"variables": len(equation["variables"]), "rows": len(rows), "degree": 4,
            "monomials": len(p), "height": max(map(abs, p.values()))}


def run(root, variant):
    path = root / variant
    source, factor, projected, final = [read(path / f) for f in ["source.json", "factored_source.json", "projected.json", "equation.json"]]
    metadata = read(root / "inherited/source_certificate.json")
    parent = read(root / "inherited/guarded.json")
    delta = read(path / "delta_certificate.json")
    receipt = {"source": source_review(parent, metadata, source, delta)}
    receipt["factor_patch"] = patch_review(source, factor, read(path / "factorization_certificate.json"))
    receipt["projection"] = projection_review(factor, projected, read(path / "projection_certificate.json"))
    receipt["translation"] = translation_review(projected, final, read(path / "translation_certificate.json"))
    receipt["metrics"] = expansion_review(final, read(path / "expanded_polynomial.json"))
    centered = root / (variant + "_centered")
    if centered.is_dir() and (centered / "equation.json").is_file():
        ce = read(centered / "equation.json")
        receipt["centered_translation"] = translation_review(projected, ce, read(centered / "translation_certificate.json"))
        receipt["centered_metrics"] = expansion_review(ce, read(centered / "expanded_polynomial.json"))
    # Deliberate semantic-data mutations are rejected with refreshed hashes.
    bad = copy.deepcopy(source)
    bad["residuals"][-1]["terms"][0][0] += 1
    changed = copy.deepcopy(delta)
    changed["target_sha256"] = digest(bad)
    try:
        source_review(parent, metadata, bad, changed)
    except ValueError:
        receipt["refreshed_hash_mutation_rejected"] = True
    else:
        raise ValueError("mutated pool survived")
    return receipt


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("root", type=Path)
    ap.add_argument("--variant", default="odd_three_pools")
    ap.add_argument("--receipt", type=Path)
    options = ap.parse_args()
    result = run(options.root, options.variant)
    result["scope"] = "New source rows, recorded inherited factorization patch, all monic eliminations, all integer translations, every SOS coefficient. Inherited factorization semantics and logical calibration are not replaced by this finite audit."
    if options.receipt:
        options.receipt.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True, indent=2))
