#!/usr/bin/env python3
"""Independent finite check of the new source delta and complete polynomial.

The producing build.py is deliberately not imported. The inherited projector's
certificate verifier is replayed, and coefficient collection below is separate
from the producer's collector. This is not a consistency decision procedure.
"""
import argparse
import copy
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "runtime"))
import terminal_elimination as E

PINS = {
    "factored_source.json": "ef999ac4bb2296a450574f0536c72aaaedb48116523f84d25184dba18c1b39f0",
    "transform_certificate.json": "218e21b1843848a21c90b67b652865f0acfa5e72bafe353a9c5fc018e9db1c76",
    "parent_equation.json": "d0ae4e3faa382d17e44932a07bcac8368e2c69b7bd24a039750601c53b47fece",
    "parent_translation.json": "15ecc7ae8b6b62663369436d9bada0938d7e419c25dd5c1eee2e39a40c522830",
    "parent_projected.json": "27c4af41ff76f651ed47c1b11fd5e8f32c91d506539c71796a73b7957977254b",
}


def need(test, message):
    if not test:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def poly(terms):
    p = defaultdict(int)
    for c, m in terms:
        p[tuple(sorted(m))] += c
    return {m: c for m, c in p.items() if c}


def add(*terms):
    p = defaultdict(int)
    for t in terms:
        for m, c in t.items():
            p[m] += c
    return {m: c for m, c in p.items() if c}


def times(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m + n))] += c * d
    return {m: c for m, c in out.items() if c}


def negative(p):
    return {m: -c for m, c in p.items()}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def var(i):
    return {(i,): 1}


def translated(p, shifts):
    total = {}
    for monomial, coefficient in p.items():
        term = {(): coefficient}
        for v in monomial:
            factor = {(v,): 1}
            if shifts.get(v):
                factor[()] = shifts[v]
            term = times(term, factor)
        total = add(total, term)
    return total


def source_check(old, source, metadata, certificate):
    grouped = certificate.get("grouped_remainders", False)
    need(type(grouped) is bool, "nonboolean grouped flag")
    expected_variables = copy.deepcopy(old["variables"])
    if grouped:
        expected_variables.extend({"name": f"symmetric_remainder.{j}.{s}", "kind": "integer_guard"}
                                  for j in range(4) for s in ("a", "b", "c"))
    need(source["variables"] == expected_variables, "source coordinate list changed")
    need(source["domain"] == "unrestricted integers", "wrong source domain")
    names = {v["name"]: i for i, v in enumerate(source["variables"])}
    A, H, f, R, h = (names[n] for n in ["shared.A", "cap.H", "cap.f", "cap.R", "cap.h"])
    C = metadata["cap_variables"]["Y"]
    anchor = poly(metadata["anchor_index"])
    indices = certificate["orientation_indices"]
    mode = certificate["mode"]
    if mode in ("linear14", "squared14"):
        need(indices == list(range(14)), "full orientation list")
    elif mode == "selected_linear":
        need(indices == [2, 3, 4, 5, 6, 8, 9, 11, 12], "nine representative indices")
    else:
        need(False, "unsupported proof mode")
    pool = {}
    for j, sd in enumerate(metadata["seed_data"]):
        x, y = sd["pair"]
        delta = add(var(y), negative(poly(sd["exponent"])))
        pool = add(pool, times(delta, delta))
        if j in indices:
            err = add({(): 1}, negative(var(x)))
            pool = add(pool, times(err, err) if mode == "squared14" else err)
    pq = metadata["pooled_quotient"]
    pool = add(pool, negative(times(add(var(A), {(): -1}), var(pq))))
    expected = {
        "cap.comparison_constructor": ("cap.deterministic_factor", add(var(f), negative(var(H)), times(var(A), var(H)))),
        "cap.index_residue": ("cap.index_residue", add(var(R), negative(anchor), negative(times(var(C), var(h))))),
        "cap.pooled_index_residue": ("cap.pooled_index_residue", pool),
    }
    changes = []
    expected_rows = []
    deleted = []
    removal = {"domain_guard." + str(j) for j in range(3, 14)} if grouped else set()
    for j, before in enumerate(old["residuals"]):
        if before["label"] in removal:
            deleted.append({"row": j, "content": before})
            continue
        if before["label"] in expected:
            label, p = expected[before["label"]]
            wanted = {"label": label, "terms": terms(p)}
            changes.append({"row": j, "before": before, "after": wanted})
            expected_rows.append(wanted)
        else:
            expected_rows.append(before)
    appended = []
    groups = []
    if grouped:
        # These four denominator groups are independently bound to the exact
        # old remainder equations, not inferred from the producer's grouping.
        bindings = [(181, [183, 236]), (189, [191, 197, 202, 207, 242]),
                    (211, [213, 219]), (223, [225, 231])]
        old_guards = metadata["guards"][3:14]
        wanted_remainders = sorted(g["pair"][0] for g in old_guards)
        need(sorted(r for d, rs in bindings for r in rs) == wanted_remainders,
             "remainder groups do not partition the old intervals")
        for j, (d, rs) in enumerate(bindings):
            for r in rs:
                guard = next(g for g in old_guards if g["pair"][0] == r)
                slack = guard["pair"][1]
                expected_bound = {(d,): 1, (r,): -1, (slack,): -1, (): -1}
                hits = [rr for rr in old["residuals"] if poly(rr["terms"]) == expected_bound]
                need(len(hits) == 1 and hits[0]["label"].endswith(".remainder_bound"),
                     "wrong source denominator for remainder")
            start = len(old["variables"]) + 3 * j
            aux = [start, start + 1, start + 2]
            pp = {(d, d): 1, (): -1}
            for r in rs:
                pp[(r, r)] = -4
            for v in aux:
                pp[(v, v)] = -1
            pp[(aux[2],)] = -1
            wanted = {"label": "symmetric_remainder_cap." + str(j), "terms": terms(pp)}
            appended.append({"row": len(expected_rows), "content": wanted})
            expected_rows.append(wanted)
            groups.append({"denominator": d, "remainders": rs, "auxiliary": aux})
        need(certificate["deleted_rows"] == deleted, "wrong interval deletion ledger")
        need(certificate["appended_rows"] == appended, "wrong cap addition ledger")
        need(certificate["remainder_groups"] == groups, "wrong remainder metadata")
        need(len(deleted) == 11, "wrong number of removed interval graphs")
        need(certificate["coordinate_added"] == list(range(len(old["variables"]), len(expected_variables))),
             "new coordinate ledger mismatch")
    need(source["residuals"] == expected_rows, "source residual list is not the exact stated transformation")
    need(certificate["changes"] == changes, "wrong change ledger")
    need(certificate["input_sha256"] == sha(old), "wrong original source hash")
    need(certificate["output_sha256"] == sha(source), "wrong output source hash")
    used = {v for r in source["residuals"] for c, m in r["terms"] for v in m}
    need(names["cap.d"] not in used, "old comparison coordinate survives")
    return len(changes)


def check(directory, negative_controls=True):
    for file, expected in PINS.items():
        need(hashlib.sha256((ROOT / "baseline" / file).read_bytes()).hexdigest() == expected,
             "baseline pin " + file)
    old = read(ROOT / "baseline/factored_source.json")
    metadata = read(ROOT / "baseline/transform_certificate.json")
    source = read(directory / "source.json")
    change = read(directory / "source_change.json")
    changed_rows = source_check(old, source, metadata, change)
    projection = read(directory / "projected.json")
    pc = read(directory / "projection_certificate.json")
    projection_result = E.verify(source, projection, pc)
    final = read(directory / "equation.json")
    tc = read(directory / "translation_certificate.json")
    need(tc["input_sha256"] == sha(projection), "translation input")
    need(tc["output_sha256"] == sha(final), "translation output")
    need(tc["convention"] == "old=new+shift", "translation convention")
    need(final["variables"] == projection["variables"], "translation variable map")
    shifts = dict(tc["shifts"])
    need(len(shifts) == len(tc["shifts"]), "duplicate coordinate shift")
    need(all(isinstance(i, int) and isinstance(d, int) and 0 <= i < len(final["variables"])
             for i, d in shifts.items()), "nonintegral translation")
    need(len(final["residuals"]) == len(projection["residuals"]), "translation row count")
    total = {}
    for j, (original, row) in enumerate(zip(projection["residuals"], final["residuals"])):
        wanted = translated(poly(original["terms"]), shifts)
        need(original["label"] == row["label"] and terms(wanted) == row["terms"], f"translation row {j}")
        need(max((len(m) for m in wanted), default=0) <= 2, "nonquadratic residual")
        total = add(total, times(wanted, wanted))
    expanded = read(directory / "expanded_polynomial.json")
    need(terms(total) == expanded["terms"], "collected coefficient list mismatch")
    count = len(final["variables"])
    used = {v for m in total for v in m}
    need(used == set(range(count)), "declared variable not used")
    metrics = read(directory / "METRICS.json")
    expected_metrics = {
        "domain": "unrestricted integers", "variables": count, "residuals": len(final["residuals"]),
        "degree": max(len(m) for m in total), "monomials": len(total),
        "coefficient_height": max(abs(c) for c in total.values()),
        "residual_coefficient_height": max(abs(c) for r in final["residuals"] for c, m in r["terms"]),
        "orientation_count": len(change["orientation_indices"]), "mode": change["mode"],
    }
    if "grouped_remainders" in metrics or change.get("grouped_remainders"):
        expected_metrics["grouped_remainders"] = change.get("grouped_remainders", False)
    need(metrics == expected_metrics, "metrics mismatch")
    rejected = []
    if negative_controls:
        labels = ["cap.deterministic_factor", "cap.index_residue", "cap.pooled_index_residue"]
        if change.get("grouped_remainders"):
            labels += ["symmetric_remainder_cap." + str(j) for j in range(4)]
        for label in labels:
            corrupt = copy.deepcopy(source)
            row = next(r for r in corrupt["residuals"] if r["label"] == label)
            row["terms"][0][0] += 1
            forged = copy.deepcopy(change)
            forged["output_sha256"] = sha(corrupt)
            for item in forged["changes"]:
                if item["after"]["label"] == label:
                    item["after"] = copy.deepcopy(row)
            for item in forged.get("appended_rows", []):
                if item["content"]["label"] == label:
                    item["content"] = copy.deepcopy(row)
            try:
                source_check(old, corrupt, metadata, forged)
            except ValueError:
                rejected.append(label)
            else:
                need(False, "corrupted source accepted")
        bad_expansion = copy.deepcopy(expanded)
        bad_expansion["terms"][0][0] += 1
        need(bad_expansion["terms"] != terms(total), "coefficient corruption undetected")
        rejected.append("expanded coefficient")
    return {"status": "PASS", "changed_source_rows": changed_rows,
            "projection": projection_result, "metrics": metrics,
            "rejected_negative_controls": rejected,
            "scope": "Finite source identities, exact projection, translation and every quartic coefficient; ordinary proof and inherited calibration are separate."}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("directories", nargs="*", type=Path)
    ap.add_argument("--receipt", type=Path)
    args = ap.parse_args()
    dirs = args.directories or [ROOT / "equations/symmetric_caps"]
    result = {str(d.name): check(d) for d in dirs}
    if args.receipt:
        args.receipt.write_bytes(canonical(result))
    print(json.dumps(result, indent=2, sort_keys=True))
