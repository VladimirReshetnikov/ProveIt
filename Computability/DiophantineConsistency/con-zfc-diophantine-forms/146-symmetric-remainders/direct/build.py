#!/usr/bin/env python3
"""Literal center and orientation reduction, then certified integral projection.

No solver or bounded refutation search is used. The input is the authenticated
factored quadratic source of the incoming 282-integer construction.
"""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "runtime"))
import terminal_elimination as E
import translate_coordinates as T


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(E.canonical_bytes(value))


def digest(value):
    return hashlib.sha256(E.canonical_bytes(value)).hexdigest()


def plus(*polys):
    out = {}
    for p in polys:
        for m, c in p.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def neg(p):
    return {m: -c for m, c in p.items()}


def V(i):
    return {(i,): 1}


GROUPS = [(181, [183, 236]), (189, [191, 197, 202, 207, 242]),
          (211, [213, 219]), (223, [225, 231])]


def create_source(mode="linear14", orientation_indices=None, grouped_remainders=False):
    old = json.loads((ROOT / "baseline/factored_source.json").read_text())
    metadata = json.loads((ROOT / "baseline/transform_certificate.json").read_text())
    eq = copy.deepcopy(old)
    eq.pop("metrics", None)
    names = {v["name"]: i for i, v in enumerate(old["variables"])}
    A = names["shared.A"]
    C = metadata["cap_variables"]["Y"]
    H = names["cap.H"]
    D = names["cap.B"]
    f = names["cap.f"]
    R = names["cap.R"]
    quotient = names["cap.h"]
    nominal = E.normalize(metadata["anchor_index"])
    # Reuse f=(1-A)H, so D=A+Hf=A+(1-A)H^2. No new coordinate.
    center_factor = plus(V(f), neg(V(H)), E.multiply(V(A), V(H)))
    residue = plus(V(R), neg(nominal), neg(E.multiply(V(C), V(quotient))))
    seed = metadata["seed_data"]
    if orientation_indices is None:
        orientation_indices = list(range(len(seed)))
    orientation_indices = sorted(orientation_indices)
    if mode not in ("linear14", "squared14", "selected_linear"):
        raise ValueError("unknown mode")
    pool = {}
    for j, sd in enumerate(seed):
        x, y = sd["pair"]
        delta = plus(V(y), neg(E.normalize(sd["exponent"])))
        pool = plus(pool, E.multiply(delta, delta))
        if j in orientation_indices:
            if mode == "squared14":
                error = plus(V(x), {(): -1})
                pool = plus(pool, E.multiply(error, error))
            else:
                pool = plus(pool, {(): 1}, neg(V(x)))
    pq = metadata["pooled_quotient"]
    pool = plus(pool, neg(E.multiply(plus(V(A), {(): -1}), V(pq))))
    replacements = {
        "cap.comparison_constructor": ("cap.deterministic_factor", center_factor),
        "cap.index_residue": ("cap.index_residue", residue),
        "cap.pooled_index_residue": ("cap.pooled_index_residue", pool),
    }
    changes = []
    for j, row in enumerate(eq["residuals"]):
        if row["label"] in replacements:
            label, p = replacements[row["label"]]
            replacement = {"label": label, "terms": E.as_terms(p)}
            changes.append({"row": j, "before": row, "after": replacement})
            eq["residuals"][j] = replacement
    if len(changes) != 3:
        raise ValueError("source row identity mismatch")
    deleted = []
    appended = []
    groups = []
    if grouped_remainders:
        removal = {"domain_guard." + str(j) for j in range(3, 14)}
        retained = []
        for j, row in enumerate(eq["residuals"]):
            if row["label"] in removal:
                deleted.append({"row": j, "content": row})
            else:
                retained.append(row)
        if len(deleted) != 11:
            raise ValueError("interval guard count mismatch")
        eq["residuals"] = retained
        for j, (denominator, remainders) in enumerate(GROUPS):
            aux = list(range(len(eq["variables"]), len(eq["variables"]) + 3))
            eq["variables"].extend({"name": f"symmetric_remainder.{j}.{s}", "kind": "integer_guard"}
                                   for s in ("a", "b", "c"))
            p = {(denominator, denominator): 1, (): -1}
            for r in remainders:
                p[(r, r)] = -4
            for v in aux:
                p[(v, v)] = -1
            p[(aux[2],)] = -1
            row = {"label": "symmetric_remainder_cap." + str(j), "terms": E.as_terms(p)}
            appended.append({"row": len(eq["residuals"]), "content": row})
            eq["residuals"].append(row)
            groups.append({"denominator": denominator, "remainders": remainders, "auxiliary": aux})
    eq["variant"] += ":deterministic_center_modC:" + mode
    if grouped_remainders:
        eq["variant"] += ":symmetric_remainder_caps"
    cert = {
        "schema": "deterministic_center_linear_orientation_v1",
        "input_sha256": digest(old), "output_sha256": digest(eq),
        "mode": mode, "orientation_indices": orientation_indices,
        "changes": changes,
        "grouped_remainders": grouped_remainders,
        "deleted_rows": deleted, "appended_rows": appended, "remainder_groups": groups,
        "center_identity": "f=(1-A)H; D=A+Hf=A+(1-A)H^2",
        "residue_modulus": "C, with |C|=Y_i(|A|), instead of 4C",
        "coordinate_added": list(range(len(old["variables"]), len(eq["variables"]))),
        "unused_comparison_coordinate": names["cap.d"],
        "semantic_proof_required": True,
    }
    return eq, cert


def build(out, mode="linear14", cap=16, orientation_indices=None, grouped_remainders=False):
    source, delta = create_source(mode, orientation_indices, grouped_remainders)
    projected, pc, _ = E.optimize(source, max_support=cap)
    E.verify(source, projected, pc)
    # Reuse only the explicit integral shifts of the parent's centered chart.
    old_projected = json.loads((ROOT / "baseline/parent_projected.json").read_text())
    old_translation = json.loads((ROOT / "baseline/parent_translation.json").read_text())
    by_name = {old_projected["variables"][i]["name"]: d
               for i, d in old_translation["shifts"]}
    shifts = {i: by_name[v["name"]] for i, v in enumerate(projected["variables"])
              if v["name"] in by_name and by_name[v["name"]]}
    final = T.translate(projected, shifts)
    expanded = E.expand(final)
    metrics = {
        "domain": "unrestricted integers", "variables": len(final["variables"]),
        "residuals": len(final["residuals"]),
        "degree": max(len(m) for c, m in expanded["terms"]),
        "monomials": len(expanded["terms"]),
        "coefficient_height": max(abs(c) for c, m in expanded["terms"]),
        "residual_coefficient_height": max(abs(c) for r in final["residuals"] for c, m in r["terms"]),
        "orientation_count": len(delta["orientation_indices"]), "mode": mode,
        "grouped_remainders": grouped_remainders,
    }
    translation = {"schema": "integral_translation_v1", "input_sha256": digest(projected),
                   "output_sha256": digest(final), "convention": "old=new+shift",
                   "shifts": [[i, s] for i, s in sorted(shifts.items())],
                   "origin": "Parent chart's shifts, matched by exact retained coordinate name."}
    for name, value in [
        ("source.json", source), ("source_change.json", delta),
        ("projected.json", projected), ("projection_certificate.json", pc),
        ("equation.json", final), ("expanded_polynomial.json", expanded),
        ("translation_certificate.json", translation), ("METRICS.json", metrics),
    ]:
        dump(out / name, value)
    print(json.dumps(metrics, sort_keys=True))
    return metrics


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=ROOT / "equations/symmetric_caps")
    ap.add_argument("--mode", choices=["linear14", "squared14", "selected_linear"], default="selected_linear")
    ap.add_argument("--cap", type=int, default=16)
    ap.add_argument("--orient", help="comma separated seed indices; only with a separate proof")
    ap.add_argument("--grouped-remainders", action=argparse.BooleanOptionalAction, default=True)
    args = ap.parse_args()
    indices = ([2, 3, 4, 5, 6, 8, 9, 11, 12] if args.mode == "selected_linear" else None) \
        if args.orient is None else [int(s) for s in args.orient.split(",")]
    build(args.output, args.mode, args.cap, indices, args.grouped_remainders)
