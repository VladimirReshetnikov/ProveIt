#!/usr/bin/env python3
"""Read-only sparse arithmetic on frozen JSON; no source/engine imports.

This records prospective residual term sets and fixed-chart polynomial
comparisons.  It does not create a source equation or run any compiler,
optimizer, factorizer, translator, centering search or satisfiability test.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "research/signed-pell-cap-projections/data"
SOURCE = ROOT / "research/signed-pell-cap-source/source.json"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(*polys):
    out = defaultdict(int)
    for p in polys:
        for m, c in p.items():
            out[m] += c
    return clean(out)


def scale(p, c):
    return clean({m: c * v for m, v in p.items()})


def mul(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m + n))] += c * d
    return clean(out)


def poly(terms):
    return add(*[{tuple(sorted(m)): c} for c, m in terms])


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def substitute(p, v, value):
    out = {}
    for m, c in p.items():
        term = {(): c}
        for w in m:
            term = mul(term, value if v == w else {(w,): 1})
        out = add(out, term)
    return out


def translate(p, shifts):
    for v, c in sorted(shifts.items()):
        p = substitute(p, v, {(v,): 1, (): c})
    return p


def squared_sum(ps):
    return add(*[mul(p, p) for p in ps])


def stats(p):
    return {"terms": len(p), "height": max(map(abs, p.values()), default=0),
            "degree": max(map(len, p), default=0)}


def coefficient_hash(p):
    b = (json.dumps(terms(p), separators=(",", ":")) + "\n").encode()
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    paths = [SOURCE, BASE / "factored_source.json", BASE / "projected.json",
             BASE / "terminal_elimination_certificate.json"]
    for chart in ("plain", "centered"):
        paths += [BASE / chart / name for name in
                  ("equation.json", "expanded_polynomial.json", "translation_certificate.json")]
    raw = {p: p.read_bytes() for p in paths}
    objects = {p: json.loads(b) for p, b in raw.items()}
    source, factored, projected, cert = [objects[p] for p in paths[:4]]
    # The literal accepted target pairs, with signs Y-k throughout.
    errors = [
        {(258,): 1, (0,): -1, (): -16},
        {(267,): 1, (25,): -2},
        {(281,): 1, (0,): -1, (4,): -1, (): -16},
    ] + [{(y,): 1, (k,): -1, (): -1} for y, k in
         [(296, 16), (310, 17), (316, 18), (322, 19), (328, 20),
          (334, 2), (340, 21), (346, 22), (352, 1), (358, 23),
          (364, 24), (370, 171)]] + [{(387,): 1, (245,): -1}]
    coupling = {(246, 395): -1, (395,): 1}
    old_pool = add(squared_sum(errors), coupling)
    need(old_pool == poly(source["residuals"][219]["terms"]), "literal source pool")
    need(old_pool == poly(factored["residuals"][217]["terms"]), "Horn pool unchanged")
    partitions = {"two_groups": [[0, 1, 3, 4, 5, 6, 7, 8],
                                 [2, 9, 10, 11, 12, 13, 14, 15]],
                  "three_groups": [[1, 3, 4, 5],
                                   [2, 6, 7, 8, 9, 10],
                                   [0, 11, 12, 13, 14, 15]],
                  "four_groups": [[2, 0, 3, 4, 5], [6, 7, 8, 9, 10],
                                  [11, 12, 13, 14, 15], [1]],
                  "five_groups": [[2, 0, 3], [4, 5, 6, 7], [8, 9, 10, 11],
                                  [12, 13, 14, 15], [1]],
                  "six_groups": [[2, 0, 3], [4, 5, 6], [7, 8, 9],
                                 [10, 11, 12], [13, 14, 15], [1]],
                  "eight_groups": [[2, 0], [3, 4], [5, 6], [7, 8],
                                   [9, 10], [11, 12], [13, 14, 15], [1]],
                  "sixteen_groups": [[i] for i in range(16) if i != 1] + [[1]]}
    report = {"schema": "inert_pooled_row_grouping_audit_v1", "status": "PASS",
              "optimized_python": not __debug__,
              "audit_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "inputs": {str(p.relative_to(ROOT)): hashlib.sha256(b).hexdigest()
                         for p, b in raw.items()},
              "source_error_terms": [terms(p) for p in errors],
              "source_coupling_terms": terms(coupling),
              "partitions": partitions, "source_groups": {}, "charts": {}}
    for name, groups in partitions.items():
        need(sorted(sum(groups, [])) == list(range(16)), "partition all errors once")
        report["source_groups"][name] = [terms(squared_sum([errors[i] for i in g])) for g in groups]
    # Replay ONLY published scalar substitutions on these error polynomials.
    # No choice enumeration or new elimination step is performed.
    minimum_support = {name: [10**9] * len(groups) for name, groups in partitions.items()}
    consumer_minimum = {name: 10**9 for name in partitions}
    post_K_minimum = {name: [10**9] * len(groups) for name, groups in partitions.items()}
    post_K_consumer = {name: 10**9 for name in partitions}
    K_restored = False
    for step in [None] + cert["steps"]:
        if step is not None:
            v, replacement = step["variable"], poly(step["restoration"])
            errors = [substitute(p, v, replacement) for p in errors]
            coupling = substitute(coupling, v, replacement)
            K_restored = K_restored or v == 25
        for name, groups in partitions.items():
            gs = [squared_sum([errors[i] for i in g]) for g in groups]
            supports = list(map(len, gs))
            minimum_support[name] = [min(a, b) for a, b in zip(minimum_support[name], supports)]
            consumer = len(add(gs[-1], coupling)) + len(groups) - 2
            consumer_minimum[name] = min(consumer_minimum[name], consumer)
            if K_restored:
                post_K_minimum[name] = [min(a, b) for a, b in zip(post_K_minimum[name], supports)]
                post_K_consumer[name] = min(post_K_consumer[name], consumer)
    retained = cert["retained_original_variables"]
    remap = {v: i for i, v in enumerate(retained)}
    def compact(p):
        need(all(v in remap for m in p for v in m), "published map covers all group ports")
        return {tuple(sorted(remap[v] for v in m)): c for m, c in p.items()}
    errors, coupling = [compact(p) for p in errors], compact(coupling)
    need(add(squared_sum(errors), coupling) == poly(projected["residuals"][130]["terms"]),
         "complete projected pool identity")
    report["published_steps_replayed_on_errors"] = len(cert["steps"])
    report["minimum_group_support_during_published_steps"] = minimum_support
    report["minimum_consumer_restoration_support_during_published_steps"] = consumer_minimum
    report["minimum_group_support_after_K_affine_restoration"] = post_K_minimum
    report["minimum_consumer_support_after_K_affine_restoration"] = post_K_consumer
    need(all(n > 16 for name in ("two_groups", "three_groups")
             for n in minimum_support[name] + [consumer_minimum[name]]), "initial groups exceed16")
    need(all(n > 16 for name in ("four_groups", "five_groups")
             for n in post_K_minimum[name][:-1] + [post_K_consumer[name]]), "post-K groups exceed16")
    for chart in ("plain", "centered"):
        equation = objects[BASE / chart / "equation.json"]
        translation = objects[BASE / chart / "translation_certificate.json"]
        shifts = dict(translation["shifts"])
        es, cp = [translate(p, shifts) for p in errors], translate(coupling, shifts)
        rows = [poly(r["terms"]) for r in equation["residuals"]]
        pool = add(squared_sum(es), cp)
        need(pool == rows[130], "complete translated pool identity")
        full = squared_sum(rows)
        need(full == poly(objects[BASE / chart / "expanded_polynomial.json"]["terms"]),
             "whole accepted quartic coefficients")
        rest = add(full, scale(mul(pool, pool), -1))
        item = {"error_terms": [terms(p) for p in es], "coupling_terms": terms(cp),
                "pool": stats(pool), "whole_accepted_quartic": stats(full), "extensions": {}}
        fixed_pool_polynomials = {"none": (full, len(equation["variables"]), len(rows))}
        for name, groups in partitions.items():
            gs = [squared_sum([es[i] for i in g]) for g in groups]
            n = len(equation["variables"])
            partials = [{(n + i,): 1} for i in range(len(gs) - 1)]
            definitions = [add(s, scale(g, -1)) for s, g in zip(partials, gs)]
            consumer = add(gs[-1], cp, *partials)
            new_rows = definitions + [consumer]
            need(add(consumer, *[scale(r, -1) for r in definitions]) == pool,
                 "universal full residual reconstruction")
            new_poly = add(rest, squared_sum(new_rows))
            removed = set(full) - set(new_poly)
            added = set(new_poly) - set(full)
            delta = add(new_poly, scale(full, -1))
            # Exact SOS difference, using the reconstructed residual.
            need(delta == add(squared_sum(new_rows), scale(mul(pool, pool), -1)),
                 "full polynomial difference")
            cross = add(*[scale(mul(gs[i], gs[j]), 2)
                          for i in range(len(gs)) for j in range(i + 1, len(gs))])
            item["extensions"][name] = {
                "group_terms": [terms(p) for p in gs],
                "new_residual_terms": [terms(p) for p in new_rows],
                "definition_supports": list(map(len, gs)),
                "consumer_restoration_support": len(consumer) - 1,
                "fixed_chart_quartic": stats(new_poly),
                "whole_quartic_coefficients_sha256": coefficient_hash(new_poly),
                "fixed_chart_declared_variables": n + len(partials),
                "fixed_chart_residuals": len(rows) + len(partials),
                "old_monomials_absent": len(removed), "new_monomials_absent_before": len(added),
                "changed_coefficients": len(delta), "cross_group_product": stats(cross)}
            fixed_pool_polynomials[name] = (new_poly, n + len(partials), len(rows) + len(partials))
        # Independently partition the ACTUAL accepted frame coefficients.
        # These are fixed-chart residual term sets, not a new semantic frame.
        frame = rows[186]
        need(equation["residuals"][186]["label"] == "shared.frame_definition", "actual frame row")
        item["frame_terms"] = terms(frame)
        item["frame_partitions"] = {}
        frame_items = sorted(frame.items())
        for count in (2, 3, 4):
            for layout in ("contiguous", "round_robin"):
                chunks = []
                for j in range(count):
                    if layout == "contiguous":
                        selected = frame_items[len(frame_items) * j // count:len(frame_items) * (j + 1) // count]
                    else:
                        selected = frame_items[j::count]
                    chunks.append(dict(selected))
                need(add(*chunks) == frame, "all frame coefficients exactly once")
                name = str(count) + "_" + layout
                entry = {"chunk_terms": [terms(p) for p in chunks],
                         "definition_supports": list(map(len, chunks[:-1])),
                         "consumer_restoration_support": len(chunks[-1]) + count - 2,
                         "combinations": {}}
                for pool_name, (pool_poly, nv, nr) in fixed_pool_polynomials.items():
                    ps = [{(nv + j,): 1} for j in range(count - 1)]
                    fs = [add(s, scale(g, -1)) for s, g in zip(ps, chunks)]
                    final = add(chunks[-1], *ps)
                    need(add(final, *[scale(f, -1) for f in fs]) == frame, "frame residual reconstruction")
                    combined = add(pool_poly, scale(mul(frame, frame), -1), squared_sum(fs + [final]))
                    entry["combinations"][pool_name] = {"fixed_chart_quartic": stats(combined),
                        "whole_quartic_coefficients_sha256": coefficient_hash(combined),
                        "fixed_chart_declared_variables": nv + count - 1,
                        "fixed_chart_residuals": nr + count - 1}
                item["frame_partitions"][name] = entry
        # A specified finite layout comparison, not an elimination/centering
        # search: rotate the fixed lexicographic frame term list and cut it
        # once, with both resulting supports strictly larger than16.
        pool_poly, nv, nr = fixed_pool_polynomials["five_groups"]
        unaffected = add(pool_poly, scale(mul(frame, frame), -1))
        best = None
        tried = 0
        for offset in range(len(frame_items)):
            rotated = frame_items[offset:] + frame_items[:offset]
            for cut in range(17, len(frame_items) - 16):
                first, last = dict(rotated[:cut]), dict(rotated[cut:])
                s = {(nv,): 1}
                rs = [add(s, scale(first, -1)), add(s, last)]
                candidate = add(unaffected, squared_sum(rs))
                measured = stats(candidate)
                score = (measured["terms"], measured["height"], offset, cut)
                tried += 1
                if best is None or score < best[0]:
                    best = (score, {"offset": offset, "cut": cut,
                        "frame_chunk_terms": [terms(first), terms(last)],
                        "new_frame_residual_terms": [terms(p) for p in rs],
                        "definition_support": len(first), "consumer_restoration_support": len(last),
                        "fixed_chart_quartic": measured,
                        "whole_quartic_coefficients_sha256": coefficient_hash(candidate),
                        "fixed_chart_declared_variables": nv + 1,
                        "fixed_chart_residuals": nr + 1})
        item["five_pool_two_frame_finite_layout_comparison"] = {
            "layouts_compared": tried, "scope": "rotations of sorted term list; one cut; supports>16",
            "best_in_this_finite_family": best[1]}
        # This maximum-coefficient monomial is untouched by all proposed rows.
        maximum = max(full, key=lambda m: abs(full[m]))
        need(maximum == (10, 10, 11, 12) if chart == "centered" else True, "centered height location")
        item["height_location"] = [full[maximum], list(maximum)]
        item["height_location_pool_contribution"] = mul(pool, pool).get(maximum, 0)
        item["height_location_frame_contribution"] = mul(frame, frame).get(maximum, 0)
        report["charts"][chart] = item
    data = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()
    if args.output.exists():
        need(args.output.read_bytes() == data, "refuse different existing output")
    else:
        args.output.write_bytes(data)
    print(json.dumps({"status": "PASS", "output_sha256": hashlib.sha256(data).hexdigest(),
                      "charts": {k: {n: v["fixed_chart_quartic"] for n, v in c["extensions"].items()}
                                 for k, c in report["charts"].items()}}, sort_keys=True))


if __name__ == "__main__":
    main()
