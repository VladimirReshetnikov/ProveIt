#!/usr/bin/env python3
"""Independent exact audit of the four signed digit caps and their export.

Only the standard library is imported. In particular this checker does not
import the producer, its elimination library, or its polynomial arithmetic.
The unbounded mathematical argument is GROUPED_SIGNED_DIGIT_CAPS.md.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def require(test, message):
    if not test:
        raise ValueError(message)


def poly(terms):
    out = defaultdict(int)
    for c, mon in terms:
        require(isinstance(c, int) and not isinstance(c, bool), "noninteger coefficient")
        require(all(isinstance(v, int) and v >= 0 for v in mon), "invalid variable")
        out[tuple(sorted(mon))] += c
    return {m: c for m, c in out.items() if c}


def add(a, b):
    out = defaultdict(int, a)
    for m, c in b.items():
        out[m] += c
    return {m: c for m, c in out.items() if c}


def mul(a, b):
    out = defaultdict(int)
    for m, c in a.items():
        for n, d in b.items():
            out[tuple(sorted(m + n))] += c*d
    return {m: c for m, c in out.items() if c}


def substitute(p, replacements):
    out = {}
    for mon, c in p.items():
        term = {(): c}
        for v in mon:
            term = mul(term, replacements.get(v, {(v,): 1}))
        out = add(out, term)
    return out


def variables(p):
    return {v for mon in p for v in mon}


def degree(p):
    return max(map(len, p), default=-1)


def load(path):
    return json.loads(path.read_text())


def hashfile(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(root):
    parent_path = root / "equations/linear9/source.json"
    target_dir = root / "equations/symmetric_caps"
    parent = load(parent_path)
    target = load(target_dir / "source.json")
    groups = [(181, [183,236]), (189, [191,197,202,207,242]),
              (211, [213,219]), (223, [225,231])]
    expected_names = {181:"pow4.output", 189:"pow6.output", 211:"pow11.output",
                      223:"pow14.output", 183:"choose0.remainder", 236:"range8.remainder",
                      191:"range0.remainder", 197:"range1.remainder", 202:"range2.remainder",
                      207:"range3.remainder", 242:"range9.remainder", 213:"range4.remainder",
                      219:"range5.remainder", 225:"range6.remainder", 231:"range7.remainder"}
    for v, name in expected_names.items():
        require(parent["variables"][v]["name"] == name, "changed semantic coordinate name")
    deleted_labels = {"domain_guard."+str(i) for i in range(3,14)}
    deleted = [(i,r) for i,r in enumerate(parent["residuals"]) if r["label"] in deleted_labels]
    require(len(deleted) == 11, "wrong deleted guard count")
    expected_pairs = [(183,184),(191,192),(197,198),(202,203),(207,208),
                      (213,214),(219,220),(225,226),(231,232),(236,237),(242,243)]
    all_private = set()
    for j, (row_id, row) in enumerate(deleted):
        u,v,w = range(547+3*j,550+3*j)
        r,s = expected_pairs[j]
        expected = {(r,s):1, (u,u):-1, (v,v):-1, (w,w):-1, (w,):-1}
        require(poly(row["terms"]) == expected, "deleted guard is not the expected product graph")
        for private in (u,v,w):
            occurrences = [i for i,r0 in enumerate(parent["residuals"])
                           if private in variables(poly(r0["terms"]))]
            require(occurrences == [row_id], "deleted guard witness is not private")
        all_private.update((u,v,w))
    remaining = [r for r in parent["residuals"] if r["label"] not in deleted_labels]
    require(target["residuals"][:len(remaining)] == remaining, "retained source rows changed")
    require(len(parent["variables"]) == 584, "unexpected raw parent coordinate count")
    require(target["variables"][:584] == parent["variables"], "old coordinates changed")
    require(len(target["variables"]) == 596, "wrong number of appended coordinates")
    require(len(target["residuals"]) == len(remaining)+4, "wrong cap count")
    for j, (den, rs) in enumerate(groups):
        u,v,w = range(584+3*j,587+3*j)
        expected = {():-1, (den,den):1, (u,u):-1, (v,v):-1, (w,w):-1, (w,):-1}
        expected.update({(r,r):-4 for r in rs})
        row = target["residuals"][len(remaining)+j]
        require(row["label"] == "symmetric_remainder_cap."+str(j), "wrong cap label")
        require(poly(row["terms"]) == expected, "wrong literal cap")
        for private in (u,v,w):
            occurrences = [i for i,r0 in enumerate(target["residuals"])
                           if private in variables(poly(r0["terms"]))]
            require(occurrences == [len(remaining)+j], "new cap witness is not fresh")
        for r in rs:
            slack = next(s for rr,s in expected_pairs if rr == r)
            expected_bound = {():-1, (den,):1, (r,):-1, (slack,):-1}
            require(sum(poly(row0["terms"]) == expected_bound
                        for row0 in target["residuals"]) == 1, "missing retained remainder bound")
    require(not any(all_private & variables(poly(r["terms"]))
                    for r in target["residuals"]), "deleted private witness remains live")

    # Replay all monic integer eliminations, without importing the producer.
    cert = load(target_dir / "projection_certificate.json")
    require(cert["input_sha256"] == hashfile(target_dir/"source.json"), "wrong source digest")
    rows = {i:poly(r["terms"]) for i,r in enumerate(target["residuals"])}
    eliminated = set()
    for step in cert["steps"]:
        rid, v = step["row_id"], step["variable"]
        require(rid in rows and v not in eliminated, "invalid repeated elimination")
        rhs = poly(step["restoration"])
        require(v not in variables(rhs), "recursive restoration")
        require(not (variables(rhs) & eliminated), "restoration uses eliminated variable")
        pivot = rows[rid]
        c = pivot.get((v,), 0)
        require(c in (-1,1), "pivot not monic over integers")
        require(all(v not in mon or mon == (v,) for mon in pivot), "nonlinear pivot occurrence")
        require(substitute(pivot, {v:rhs}) == {}, "restoration does not solve pivot")
        del rows[rid]
        rows = {i:substitute(r, {v:rhs}) for i,r in rows.items()}
        require(all(degree(r)<=2 for r in rows.values()), "projection exceeds quadratic degree")
        eliminated.add(v)
    kept_vars = cert["retained_original_variables"]
    kept_rows = cert["retained_original_rows"]
    require(kept_rows == sorted(rows), "wrong retained row list")
    live = set().union(*(variables(r) for r in rows.values()))
    require(kept_vars == sorted(live), "retained variables do not equal live variables")
    unconstrained = set(cert["unconstrained_removed"])
    require(unconstrained == set(range(596))-eliminated-live, "wrong unconstrained variable removal")
    remap = {old:new for new,old in enumerate(kept_vars)}
    projected = load(target_dir/"projected.json")
    require(projected["variables"] == [target["variables"][v] for v in kept_vars], "variable metadata mismatch")
    require(len(projected["residuals"]) == len(kept_rows), "projected row count mismatch")
    for out, rid in zip(projected["residuals"], kept_rows):
        remapped = {tuple(remap[v] for v in mon):c for mon,c in rows[rid].items()}
        require(poly(out["terms"]) == remapped, "wrong projected row")
        require(out["label"] == target["residuals"][rid]["label"], "wrong projected label")
    require(cert["output_sha256"] == hashfile(target_dir/"projected.json"), "wrong projection digest")

    # Replay all integral translations, including translations of the cap inputs.
    trans = load(target_dir/"translation_certificate.json")
    require(trans["convention"] == "old=new+shift", "unknown translation convention")
    shifts = {v:{():s, (v,):1} for v,s in trans["shifts"]}
    require(len(shifts) == len(trans["shifts"]), "duplicate translation coordinate")
    final = load(target_dir/"equation.json")
    require(projected["variables"] == final["variables"], "translation changed coordinate metadata")
    require(len(projected["residuals"]) == len(final["residuals"]), "translation changed row count")
    for before, after in zip(projected["residuals"], final["residuals"]):
        require(before["label"] == after["label"], "translation changed row label")
        require(substitute(poly(before["terms"]), shifts) == poly(after["terms"]), "translation not exact")
    require(trans["input_sha256"] == hashfile(target_dir/"projected.json"), "translation input digest")
    require(trans["output_sha256"] == hashfile(target_dir/"equation.json"), "translation output digest")

    expanded = {}
    final_rows = [poly(r["terms"]) for r in final["residuals"]]
    for r in final_rows:
        require(degree(r)<=2, "nonquadratic final row")
        expanded = add(expanded, mul(r,r))
    published = load(target_dir/"expanded_polynomial.json")
    require(expanded == poly(published["terms"]), "collected polynomial mismatch")
    live_final = set().union(*(variables(r) for r in final_rows))
    require(live_final == set(range(len(final["variables"]))), "unused final variable")
    metrics = {"variables":len(final["variables"]), "residuals":len(final_rows),
               "degree":degree(expanded), "monomials":len(expanded),
               "coefficient_height":max(map(abs,expanded.values())),
               "residual_coefficient_height":max(abs(c) for r in final_rows for c in r.values())}
    advertised = load(target_dir/"METRICS.json")
    for k,v in metrics.items():
        require(advertised[k] == v, "incorrect reported metric "+k)
    require(metrics == {"variables":260,"residuals":185,"degree":4,"monomials":5099,
                        "coefficient_height":128446,"residual_coefficient_height":256}, "unexpected endpoint")
    return {"status":"passed", "scope":"Four literal caps; retained source; private witnesses; all monic integer restorations; all integral translations; every quartic coefficient.",
            "metrics":metrics, "deleted_private_witnesses":len(all_private),
            "new_private_witnesses":12, "monic_restorations":len(cert["steps"]),
            "unconstrained_removed":len(unconstrained),
            "inputs":{str(p.relative_to(root)):hashfile(p) for p in [parent_path,
                target_dir/"source.json",target_dir/"projection_certificate.json",
                target_dir/"translation_certificate.json",target_dir/"equation.json",
                target_dir/"expanded_polynomial.json"]},
            "mathematics":"Unbounded correctness is proved separately in GROUPED_SIGNED_DIGIT_CAPS.md; this checker does not prove consistency or the inherited calibration."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(args.root)
    text = json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text)
