#!/usr/bin/env python3
"""Literal audit of the fixed-base/binomial-weight signed-power interface.

Adapted from the inherited independent factorial-free interface checker.
This checker imports no construction or transformation module.  Its request
table is stated here independently.  It checks the raw source before monic
projection; the separate certificate audit must check transport to the final
quartic.  These finite checks do not certify the mathematical Pell theorem or
the C222/ZFC calibration.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def add(*polys):
    out = defaultdict(int)
    for p in polys:
        for m, c in p.items():
            out[m] += c
    return {m: c for m, c in out.items() if c}


def scale(p, c):
    return {m: c * a for m, a in p.items() if c * a}


def mul(p, q):
    out = defaultdict(int)
    for m, a in p.items():
        for n, b in q.items():
            out[tuple(sorted(m + n))] += a * b
    return {m: c for m, c in out.items() if c}


def sq(p):
    return mul(p, p)


def const(c):
    return {(): c} if c else {}


def var(i):
    return {(i,): 1}


def normalize(terms):
    return add(*[{tuple(sorted(m)): c} for c, m in terms])


def require_equal(actual, expected, label):
    difference = add(actual, scale(expected, -1))
    if difference:
        raise ValueError((label, "polynomial difference", difference))


def audit(path):
    raw = path.read_bytes()
    src = json.loads(raw)
    variables = src["variables"]
    names = {v["name"]: i for i, v in enumerate(variables)}
    labels = defaultdict(list)
    for row in src["residuals"]:
        labels[row["label"]].append(normalize(row["terms"]))

    def row(name):
        if len(labels[name]) != 1:
            raise ValueError(("nonunique row", name, len(labels[name])))
        return labels[name][0]

    def vv(name):
        return var(names[name])

    t = add(vv("t0"), const(16))
    x, y = vv("x"), vv("y")
    rb = vv("beta.RB")
    radius = vv("radius.R")
    b = vv("choose0.output")
    q = vv("pow2.output")
    a = vv("shared.A")
    base = const(16)
    bh = vv("self_radix.BH")
    reps = [add(var(i), const(1)) for i in range(16, 25)]
    anchor_index = add(vv("add.380"), const(1))

    if labels["growth.base_definition"] or labels["growth.majorant_definition"]:
        raise ValueError("obsolete separate F/U majorant definition remains")
    old_u = names["growth.power_U"]
    if any(old_u in m for rows in labels.values() for p in rows for m in p):
        raise ValueError("old independent U coordinate remains live")
    require_equal(
        row("cofinal.horizon"),
        add(vv("t0"), scale(sq(vv("cofinal.horizon_root")), -1)),
        "cofinal horizon",
    )
    require_equal(
        row("self_radix.base_definition"),
        add(bh, scale(rb,-2), scale(mul(b, add(const(2), scale(t,2), *reps)), -1)),
        "H=2+2(R+t)+sum actual representatives with RB shared",
    )
    require_equal(
        row("radix.progression"),
        add(q, scale(vv("radix.progression_parameter"), -6), const(-3)),
        "radix q=6z+3",
    )
    require_equal(
        row("beta.odd_square_multiplier"),
        add(vv("beta.odd_square_multiplier"), scale(sq(add(scale(vv("beta.odd_square_root_half"), 2), const(1))), -1)),
        "odd-square beta multiplier",
    )
    require_equal(
        row("bootstrap.beta_base_fixed_radius"),
        add(y, scale(mul(rb, vv("beta.odd_square_multiplier")), -1)),
        "y=RB times beta multiplier",
    )
    require_equal(row("beta.RB"),add(rb,scale(mul(radius,b),-1)),"RB shared product")

    # Every row below is (base, exponent, output, principal-pair prefix).
    # Call 6 uses the one-step addition from the t-index pair.
    output = lambda k: radius if k == 0 else vv(f"pow{k}.output")
    requests = [
        (base, t, output(0), "index0"),
        (b, x, output(1), "index12"),
        (bh, x, output(2), "index12"),
        (add(q, const(1)), add(radius, t), output(3), "index2"),
        (q, t, output(4), "index0"),
        (add(q, const(1)), reps[0], output(5), "index3"),
        (q, add(t, const(1)), output(6), None),
        (add(q, const(1)), reps[1], output(7), "index5"),
        (add(q, const(1)), reps[2], output(8), "index6"),
        (add(q, const(1)), reps[3], output(9), "index7"),
        (add(q, const(1)), reps[4], output(10), "index8"),
        (q, add(y, const(1)), output(11), "index9"),
        (add(q, const(1)), reps[5], output(12), "index10"),
        (add(q, const(1)), reps[6], output(13), "index11"),
        (q, x, output(14), "index12"),
        (add(q, const(1)), reps[7], output(15), "index13"),
        (add(q, const(1)), reps[8], output(16), "index14"),
        (add(q, const(1)), anchor_index, output(17), "index15"),
    ]
    atoms = {tuple(sorted(p.items())): p for n, k, m, _ in requests for p in (n, k, m)}
    expected_frame = add(vv("shared.W"), const(-2), *[scale(sq(p), -1) for p in atoms.values()])
    require_equal(row("shared.frame_definition"), expected_frame, "complete square frame")

    # Multiplication rows are elementary definitions.  Unfold just the small
    # Pell-side gate expressions, retaining all front atoms and pair variables.
    gate_defs = {}
    for p in labels["multiplication"]:
        candidates = [m[0] for m, c in p.items() if len(m) == 1 and c == 1 and variables[m[0]]["kind"] == "gate"]
        if len(candidates) != 1:
            raise ValueError(("ambiguous multiplication row", p))
        i = candidates[0]
        if any(i in m for m in p if m != (i,)) or i in gate_defs:
            raise ValueError(("nonfunctional multiplication row", i))
        gate_defs[i] = scale(add(p, scale(var(i), -1)), -1)
    stop = {i for n, k, m, _ in requests for p in (n, k, m) for mon in p for i in mon}
    stop.add(names["shared.A"])
    derived_d = names["index_addition.D"]
    gate_defs[derived_d] = add(sq(a), const(-1))

    def expand(p, stack=()):
        terms = []
        for mon, coeff in p.items():
            product = const(coeff)
            for i in mon:
                if i in gate_defs and i not in stop:
                    if i in stack:
                        raise ValueError(("cyclic gate", stack, i))
                    factor = expand(gate_defs[i], stack + (i,))
                else:
                    factor = var(i)
                product = mul(product, factor)
            terms.append(product)
        return add(*terms)

    require_equal(expand(row("index_addition.D_definition")), {}, "Pell addition D=A^2-1")
    principal = {}
    for _, exponent, _, prefix in requests:
        if prefix is not None:
            if prefix in principal:
                require_equal(principal[prefix], exponent, "shared-index exponent")
            principal[prefix] = exponent
    pool = []
    for prefix, exponent in principal.items():
        xp, yp = vv(prefix + ".X"), vv(prefix + ".Y")
        norm = add(sq(xp), sq(yp), scale(mul(sq(a), sq(yp)), -1), const(-1))
        require_equal(expand(row(prefix + ".norm1")), norm, prefix + " norm")
        pool.extend([sq(add(xp, const(-1))), sq(add(yp, scale(exponent, -1)))])
    pool.append(scale(mul(add(a, const(-1)), vv("cap.pooled_quotient")), -1))
    require_equal(row("cap.pooled_index_residue"), add(*pool), "all fourteen paired signed indices")

    bases = [base, b, bh, add(q, const(1)), q]
    for index, n in enumerate(bases):
        modulus = vv(f"base{index}.T")
        expected = add(scale(mul(a, n), 2), scale(sq(n), -1), const(-1), scale(modulus, -1))
        require_equal(expand(row(f"base{index}.T_definition")), expected, f"base{index} modulus")
    call_base = [0, 1, 2, 3, 4, 3, 4, 3, 3, 3, 3, 4, 3, 3, 4, 3, 3, 3]
    for call, (n, _, m, prefix) in enumerate(requests):
        if prefix is None:
            xt, yt = vv("index0.X"), vv("index0.Y")
            xp = add(mul(a, xt), mul(add(sq(a), const(-1)), yt))
            yp = add(xt, mul(a, yt))
        else:
            xp, yp = vv(prefix + ".X"), vv(prefix + ".Y")
        expected = add(xp, scale(mul(a, yp), -1), mul(n, yp), scale(m, -1), scale(mul(vv(f"base{call_base[call]}.T"), vv(f"pow{call}.quotient")), -1))
        require_equal(expand(row(f"pow{call}.power_congruence")), expected, f"power request {call}")

    return {
        "status": "passed",
        "raw_source_sha256": hashlib.sha256(raw).hexdigest(),
        "requests_checked": len(requests),
        "distinct_frame_atoms": len(atoms),
        "principal_pairs_checked": len(principal),
        "base_moduli_checked": len(bases),
        "one_step_derived_pair_checked": True,
        "front_bootstrap_rows_checked": True,
        "compiler_imports": False,
        "scope": "Raw fixed-base16/binomial-weight power interface; mathematical soundness, calibration, and projection are separate obligations.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?", default=Path(__file__).resolve().parent.parent/'stages/fixed_base/raw_source.json', help="raw source; default ../stages/fixed_base/raw_source.json relative to this script")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = audit(args.source)
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
