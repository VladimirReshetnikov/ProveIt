#!/usr/bin/env python3
"""Independently replay the complete parent-to-strict raw-source edit.

Imports only the independent sparse-polynomial checker, no producer.
Unbounded arithmetic justifying these literal changes is in report/main.tex.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
from check_endpoints import norm, add, subst, require

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "sources/factorial_free/direct/factorial_free_affine/raw_source.json"
SOURCE = ROOT / "direct/source/raw_source.json"
PARENT_HASH = "7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855"


def terms(poly):
    return [[coefficient, list(monomial)] for monomial, coefficient in sorted(poly.items())]


def verify(actual=None):
    require(hashlib.sha256(PARENT.read_bytes()).hexdigest() == PARENT_HASH,
            "literal parent identity")
    old = json.loads(PARENT.read_text())
    source = json.loads(SOURCE.read_text()) if actual is None else actual
    names = {v["name"]: i for i, v in enumerate(old["variables"])}
    t = names["t0"]
    f = names["crt.growth_majorant_F"]
    radius = names["mul.1"]
    base = names["growth.power_base"]
    q = names["pow2.output"]
    z = names["radix.odd_square_root_half"]
    qt, qt1 = names["pow4.output"], names["pow6.output"]
    ratio_t = names["remainder_budget.ratio0"]
    ratio_t1 = names["remainder_budget.ratio1"]
    removed = set(range(239, 247)) | {376}
    require(old["residuals"][376]["label"] == "remainder_budget.ratio1",
            "removed ratio identity")
    require(old["residuals"][246]["label"] == "pow6.power_congruence",
            "removed power identity")
    rows = []
    changed = []
    for i, row in enumerate(old["residuals"]):
        if i in removed:
            continue
        p = norm(row["terms"])
        label = row["label"]
        if label == "growth.base_definition":
            p = {(base,): 1, (t,): -1, (): -16}
        elif label == "radix.odd_square":
            p = {(q,): 1, (z,): -4, (): -1}
            label = "radix.affine_class"
        elif p == {(radius,): 1, (f, f): -1}:
            p = {(radius,): 1, (f,): -1}
            label = "crt.linear_radius"
        elif label == "shared.frame_definition":
            # Actual t=t0+16: the deleted successor index is t0+17.
            p = add(p, {(t, t): 1, (t,): 34, (): 289,
                        (qt1, qt1): 1, (base, base): 1})
        p = subst(p, qt1, {(qt,): 1})
        p = subst(p, ratio_t1, {(ratio_t,): 1})
        result = {"label": label, "terms": terms(p)}
        rows.append(result)
        if result != row:
            changed.append({"row": i, "old": row, "new": result})
    expected = copy.deepcopy(old)
    expected["variant"] += ":strict_horizon_ranges"
    expected["residuals"] = rows
    require(expected == source, "complete strict raw source differs")
    ledger = json.loads((ROOT / "direct/source/mutation.json").read_text())
    require(ledger["source_sha256"] == PARENT_HASH, "mutation parent hash")
    require(ledger["removed_rows"] == sorted(removed), "deletion census")
    require(ledger["changes"] == changed, "complete change census")
    require(ledger["base_offset"] == 0, "selected self-power base")
    require(ledger["range_aliases"] == [[qt1, qt], [ratio_t1, ratio_t]],
            "range aliases")
    return len(changed), len(removed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    changed, deleted = verify()
    source = json.loads(SOURCE.read_text())
    controls = []
    bad = copy.deepcopy(source)
    next(r for r in bad["residuals"] if r["label"] == "growth.base_definition")["terms"][0][0] += 1
    altered = [("changed self-power base", bad)]
    bad = copy.deepcopy(source)
    bad["residuals"].append(json.loads(PARENT.read_text())["residuals"][246])
    altered.append(("reintroduced successor-power request", bad))
    bad = copy.deepcopy(source)
    bad["residuals"][40]["terms"][0][0] += 1
    altered.append(("changed untouched calibrated arithmetic", bad))
    for description, bad in altered:
        try:
            verify(bad)
        except ValueError:
            controls.append(description)
        else:
            raise ValueError("Corruption was accepted: " + description)
    result = {"status": "PASS", "imports_no_producer_modules": True,
              "parent_sha256": PARENT_HASH,
              "raw_source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              "changed_rows": changed, "deleted_rows": deleted,
              "all_untouched_rows_and_metadata_identical": True,
              "negative_controls_rejected": controls,
              "scope": "Literal source identity; arithmetic semantics are separate ordinary proofs."}
    output = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
