#!/usr/bin/env python3
"""Independent literal, algebra, and positivity audit; imports no builder.

This is finite verification of the emitted certificates, not an end-to-end
formal proof of the inherited numerical calculus or Pell theorems.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
import json
from math import comb
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(a, b, scale=1):
    out = defaultdict(int, a)
    for m, c in b.items():
        out[m] += scale * c
    return clean(out)


def mul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return clean(out)


def scalar(c):
    return {} if not c else {(): c}


def var(i):
    return {(i,): 1}


def atom(a):
    return scalar(a[1]) if a[0] == "c" else var(a[1])


def square(p):
    return mul(p, p)


def product(ps):
    out = scalar(1)
    for p in ps:
        out = mul(out, p)
    return out


def polynomial(terms):
    require(len({tuple(m) for c, m in terms}) == len(terms), "duplicate monomial")
    return {tuple(m): c for c, m in terms if c}


def substitute(p, replacements):
    out = {}
    for mon, coefficient in p.items():
        term = scalar(coefficient)
        for i in mon:
            term = mul(term, replacements[i])
        out = add(out, term)
    return out


def sparse(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]


def count_and_expand(equation, expanded):
    n = len(equation["variables"])
    require(equation["domain"] == "nonnegative integers", "wrong domain")
    names = [v["name"] for v in equation["variables"]]
    require(len(set(names)) == n, "duplicate coordinate name")
    p = {}
    used = set()
    max_row = 0
    for row in equation["residuals"]:
        r = polynomial(row["terms"])
        require(r and all(len(m) <= 2 for m in r), "nonquadratic or empty row")
        require(all(0 <= j < n for m in r for j in m), "coordinate outside range")
        used.update(j for m in r for j in m)
        max_row = max(max_row, max(abs(c) for c in r.values()))
        p = add(p, square(r))
    require(used == set(range(n)), "unused listed coordinate")
    require(expanded["terms"] == sparse(p), "expanded polynomial mismatch")
    metrics = {"variables": n, "quadratic_rows": len(equation["residuals"]),
               "exact_degree": max(map(len, p)), "expanded_monomials": len(p),
               "max_abs_row_coefficient": max_row,
               "max_abs_expanded_coefficient": max(map(abs, p.values()))}
    for key, value in metrics.items():
        require(equation["metrics"][key] == value, "metric mismatch: " + key)
    return metrics


class Trace:
    def __init__(self, data):
        self.data = data
        self.variables = data["raw_variables"]
        self.rows = data["raw_rows"]
        self.by_label = defaultdict(list)
        self.defs = {}
        for r in self.rows:
            p = polynomial(r["terms"])
            self.by_label[r["label"]].append(p)
            if r["gate"] is not None:
                i = r["gate"]
                require(self.variables[i]["kind"] == "gate", "gate kind mismatch")
                require(p.get((i,)) == 1, "gate not monic")
                q = {m: -c for m, c in p.items() if m != (i,)}
                require(all(c >= 0 and all(j < i for j in m) for m, c in q.items()),
                        "gate not natural and triangular")
                require(all(len(m) <= 2 for m in q), "gate exceeds degree two")
                require(i not in self.defs, "duplicate gate definition")
                self.defs[i] = q
        require(set(self.defs) == {int(i) for i in data["raw_gate_map"]},
                "trace gate map disagrees")

    def expand(self, p, frozen=()):
        frozen = set(frozen)
        @lru_cache(None)
        def value(i):
            if i in frozen or i not in self.defs:
                return var(i)
            out = {}
            for mon, c in self.defs[i].items():
                out = add(out, product([scalar(c)] + [value(j) for j in mon]))
            return out
        return substitute(p, {i: value(i) for m in p for i in m})

    def identity(self, label, expected, frozen):
        require(len(self.by_label[label]) == 1, "missing/duplicate row: " + label)
        require(self.expand(self.by_label[label][0], frozen) == expected,
                "transcription mismatch: " + label)

    def expression(self, target, expected, frozen):
        keep = set(frozen)
        if target[0] == "v":
            keep.discard(target[1])
        require(self.expand(atom(target), keep) == expected,
                "expression transcription mismatch at " + str(target))


def ids(atoms):
    return {a[1] for a in atoms if a[0] == "v"}


def norm(a, x, y):
    return add(add(square(x), square(y)),
               add(scalar(1), mul(square(a), square(y))), -1)


def replay_affine_projection(trace, equation):
    # This implementation works from the recorded quadratic row data only.
    # It does not execute the author compiler or import its functions.
    substitutions = {}
    removed = set()
    gates = trace.defs
    for i in range(len(trace.variables)):
        replacement = None
        if i in gates and all(len(m) <= 1 for m in gates[i]):
            candidate = substitute(gates[i], substitutions)
            require(all(c >= 0 and len(m) <= 1 for m, c in candidate.items()),
                    "invalid affine restoration")
            if len(candidate) <= 4:
                replacement = candidate
                removed.add(i)
        substitutions[i] = replacement if replacement is not None else var(i)
    rows = []
    for r in trace.rows:
        if r["gate"] in removed:
            continue
        p = substitute(polynomial(r["terms"]), substitutions)
        if p:
            require(max(map(len, p)) <= 2, "affine substitution raised degree")
            rows.append((r["label"], r["gate"], p))
    definers = {g: j for j, (_, g, _) in enumerate(rows) if g is not None}
    needed = {j for j, (_, g, _) in enumerate(rows) if g is None}
    variables = {i for j in needed for m in rows[j][2] for i in m}
    pending = list(variables)
    while pending:
        i = pending.pop()
        j = definers.get(i)
        if j is None or j in needed:
            continue
        needed.add(j)
        for m in rows[j][2]:
            for k in m:
                if k not in variables:
                    variables.add(k)
                    pending.append(k)
    ordered = sorted(variables)
    remap = {v: i for i, v in enumerate(ordered)}
    expected_rows = [{"label": label,
                      "terms": [[c, [remap[i] for i in m]]
                                for m, c in sorted(p.items())]}
                     for j, (label, _, p) in enumerate(rows) if j in needed]
    require(equation["variables"] == [trace.variables[i] for i in ordered],
            "affine-projected coordinate list mismatch")
    require(equation["residuals"] == expected_rows, "affine-projected rows mismatch")
    return {"affine_coordinates_removed": len(removed),
            "restoration": "nonnegative affine integer polynomials"}


def audit_radix(trace):
    data = trace.data
    radix = data["common_radix"]
    powers = [p for p in data["macro_log"] if p["macro"] in ("power", "shared_power")]
    choose = [p for p in data["macro_log"] if p["macro"] == "binomial"]
    lookup = {(tuple(p["base"]), tuple(p["exponent"])): p["output"] for p in powers}
    exponent = {}
    for n in radix["upper_arguments"]:
        exponent = add(exponent, atom(n))
    trace.expression(radix["exponent"], exponent, ids(radix["upper_arguments"]))
    key = (("c", 2), tuple(radix["exponent"]))
    require(key in lookup, "missing common radix power")
    radix_power = lookup[key]
    trace.expression(radix["radix"], add(atom(radix_power), scalar(1)), ids([radix_power]))
    require([c["n"] for c in choose] == radix["upper_arguments"], "binomial upper ledger mismatch")
    names = {v["name"]: ["v", i] for i, v in enumerate(trace.variables)}
    for c in choose:
        out, n, k, q = [c[key] for key in ("output", "n", "k", "radix")]
        require(q == radix["radix"], "binomial uses a different radix")
        tag = trace.variables[out[1]]["name"].removesuffix(".output")
        # Identify the one numerator power whose base is exactly q+1.
        numerators = []
        for power in powers:
            if power["exponent"] != n:
                continue
            if trace.expand(atom(power["base"]), ids([q])) == add(atom(q), scalar(1)):
                numerators.append(power["output"])
        require(len(numerators) == 1, "missing or ambiguous binomial numerator")
        numerator = numerators[0]
        denominator = lookup[(tuple(q), tuple(k))]
        h, r, rs, os = [names[tag + "." + s]
                        for s in ("high", "remainder", "rslack", "oslack")]
        frozen = ids([out, q, numerator, denominator, h, r, rs, os])
        expected = add(atom(numerator), add(mul(atom(denominator),
                       add(mul(atom(q), atom(h)), atom(out))), atom(r)), -1)
        trace.identity(tag + ".digit_division", expected, frozen)
        trace.identity(tag + ".remainder_bound",
                       add(atom(denominator), add(add(atom(r), atom(rs)), scalar(1)), -1), frozen)
        trace.identity(tag + ".digit_bound",
                       add(atom(q), add(add(atom(out), atom(os)), scalar(1)), -1), frozen)
    return {"binomial_graphs": len(choose), "power_graphs": len(powers),
            "distinct_lower_arguments": len({tuple(c["k"]) for c in choose})}


def audit_offsets(trace):
    offset_ids = set()
    for c in trace.data["congruences"]:
        left, right, m, q, offset = [c[key] for key in
                                     ("left", "right", "modulus", "quotient", "common_offset")]
        offset_ids.add(tuple(offset))
        expected = add(add(atom(left), mul(atom(m), atom(q))),
                       add(atom(right), mul(atom(m), atom(offset))), -1)
        trace.identity(c["label"], expected, ids([left, right, m, q, offset]))
    require(len(offset_ids) <= 1, "offset was not shared")
    # Finite negative/zero modulus controls of the general integer identity.
    cases = 0
    for modulus in range(-3, 4):
        for lp in range(4):
            for lm in range(4):
                left, right = modulus * (lm-lp), 0
                offset = 4
                quotient = lp + offset-lm
                require(quotient >= 0 and left + modulus*quotient == right + modulus*offset,
                        "common-offset fixture")
                cases += 1
    return {"congruences": len(trace.data["congruences"]),
            "shared_offsets": len(offset_ids), "signed_controls": cases}


def audit_frame(trace):
    frame = trace.data["shared_frame"]
    if frame is None:
        return {"present": False}
    power = [p for p in trace.data["macro_log"] if p["macro"] == "shared_power"]
    W, A, Z, U, V, B, P = [frame[key] for key in ("W", "A", "Z", "U", "V", "B", "P")]
    groups = frame["index_groups"]
    congruences = {c["label"]: c for c in trace.data["congruences"]}
    def congruence(label, left, right, modulus, frozen):
        c = congruences[label]
        quotient, offset = c["quotient"], c["common_offset"]
        expected = add(add(left, mul(modulus, atom(quotient))),
                       add(right, mul(modulus, atom(offset))), -1)
        trace.identity(label, expected, set(frozen) | ids([quotient, offset]))
    ports = [p[key] for p in power for key in ("base", "exponent", "output")]
    bound = scalar(1)
    for a in ports:
        bound = add(bound, atom(a))
    trace.expression(W, bound, ids(ports))
    trace.expression(A, add(atom(frame["A_slack"]), scalar(2)), ids([frame["A_slack"]]))
    trace.expression(P, product(atom(g["Y"]) for g in groups), ids(g["Y"] for g in groups))
    trace.expression(V, mul(square(atom(P)), add(atom(frame["V_slack"]), scalar(1))),
                     ids([P, frame["V_slack"]]))
    trace.expression(B, add(scalar(1), product([scalar(4), atom(P),
                         add(atom(frame["B_slack"]), scalar(1))])), ids([P, frame["B_slack"]]))
    trace.identity("frame.auxiliary_norm", norm(atom(A), atom(U), atom(V)), ids([A, U, V]))
    trace.identity("frame.last_norm", norm(add(atom(W), scalar(1)), atom(A), mul(atom(W), atom(Z))),
                   ids([W, A, Z]))
    congruence("frame.B_mod_U", atom(B), atom(A), atom(U), ids([B, A, U]))
    by_group = {g["tag"]: g for g in groups}
    for g in groups:
        k, X, Y, S, R, ys = [g[key] for key in ("k", "X", "Y", "S", "R", "Y_slack")]
        trace.expression(Y, add(atom(k), atom(ys)), ids([k, ys]))
        trace.identity(g["tag"] + ".norm1", norm(atom(A), atom(X), atom(Y)), ids([A, X, Y]))
        trace.identity(g["tag"] + ".norm3", norm(atom(B), atom(S), atom(R)), ids([B, S, R]))
        congruence(g["tag"] + ".S_mod_U", atom(S), atom(X), atom(U), ids([S, X, U]))
        congruence(g["tag"] + ".R_mod_4Y", atom(R), atom(k), mul(scalar(4), atom(Y)),
                   ids([R, k, Y]))
    for p in power:
        n, k, m, T = [p[key] for key in ("base", "exponent", "output", "T")]
        g = by_group[p["group"]]
        require(k == g["k"], "power uses wrong Pell index group")
        tag = trace.variables[m[1]]["name"].removesuffix(".output")
        expected = add(product([scalar(2), atom(A), atom(n)]),
                       add(add(atom(T), square(atom(n))), scalar(1)), -1)
        trace.identity(tag + ".T_definition", expected, ids([A, n, T]))
        X, Y = g["X"], g["Y"]
        congruence(tag + ".power_congruence", add(atom(X), mul(atom(Y), atom(n))),
                   add(mul(atom(Y), atom(A)), atom(m)), atom(T), ids([X, Y, n, A, m, T]))
    require(not any("output_bound" in r["label"] for r in trace.rows),
            "obsolete local output bound remains")
    return {"present": True, "power_graphs": len(power), "index_groups": len(groups),
            "all_outputs_in_global_bound": True, "local_output_bound_rows": 0}


def positivity(trace):
    # Every exponent must be positive before any power theorem is used:
    # this supplies Y_j>=k_j>0 and hence P>0 in the shared frame.
    power = [p for p in trace.data["macro_log"] if p["macro"] in ("power", "shared_power")]
    factorial = [p for p in trace.data["macro_log"] if p["macro"] == "factorial"]
    proved = set()
    choose = [p for p in trace.data["macro_log"] if p["macro"] == "binomial"]
    protected = ids([p[key] for p in power for key in ("base", "exponent", "output")] +
                    [c[key] for c in choose for key in ("n", "k", "output")])
    def expand_port(a, extra=()):
        frozen = protected | ids(extra)
        if a[0] == "v":
            frozen.discard(a[1])
        return trace.expand(atom(a), frozen)
    factorial_numerators = {}
    for f in factorial:
        tag = trace.variables[f["output"][1]]["name"].removesuffix(".output")
        n, out = f["n"], f["output"]
        radius_candidates = [p for p in power
                             if p["base"] == p["exponent"] and
                             expand_port(p["base"], [n]) == add(atom(n), scalar(2))]
        require(len(radius_candidates) == 1, "factorial radius power mismatch")
        radius = radius_candidates[0]["output"]
        numerators = [p for p in power if p["exponent"] == n and
                      expand_port(p["base"], [radius]) == add(atom(radius), scalar(1))]
        require(len(numerators) == 1, "factorial numerator power mismatch")
        numerator = numerators[0]["output"]
        bins = [c for c in choose if c["k"] == n and
                expand_port(c["n"], [n, radius]) == add(atom(n), atom(radius))]
        require(len(bins) == 1, "factorial binomial graph mismatch")
        c = bins[0]["output"]
        names = {v["name"]: ["v", i] for i, v in enumerate(trace.variables)}
        r, s = [names[tag + "." + name] for name in ("remainder", "slack")]
        frozen = ids([numerator, c, out, r, s])
        trace.identity(tag + ".ceiling", add(add(atom(numerator), atom(c)),
                       add(add(mul(atom(c), atom(out)), atom(r)), scalar(1)), -1), frozen)
        trace.identity(tag + ".remainder_bound", add(atom(c),
                       add(add(atom(r), atom(s)), scalar(1)), -1), frozen)
        factorial_numerators[tuple(out)] = numerator
    def lower(a):
        @lru_cache(None)
        def at(i):
            if i in proved:
                return 1
            if i not in trace.defs:
                return 0
            total = 0
            for mon, c in trace.defs[i].items():
                term = c
                for j in mon:
                    term *= at(j)
                total += term
            return min(total, 2)
        return min(a[1], 2) if a[0] == "c" else at(a[1])
    require(all(lower(p["exponent"]) >= 1 for p in power),
            "an exponent lacks a prior positivity proof")
    rounds = []
    todo_power = list(power)
    todo_factorial = list(factorial)
    # A factorial f is positive from its ceiling rows once the numerator
    # power is positive: c(f-1)<Pnum, Pnum>0, c>0.
    while todo_power or todo_factorial:
        progress = []
        for p in list(todo_power):
            if lower(p["base"]) >= 1:
                proved.add(p["output"][1])
                todo_power.remove(p)
                progress.append(trace.variables[p["output"][1]]["name"])
        for f in list(todo_factorial):
            tag = trace.variables[f["output"][1]]["name"].removesuffix(".output")
            n = f["n"]
            numerator = factorial_numerators[tuple(f["output"])]
            if lower(numerator) >= 1 and lower(n) >= 1:
                proved.add(f["output"][1])
                todo_factorial.remove(f)
                progress.append(tag + ".positive_by_ceiling")
        require(progress, "positivity induction stalled")
        rounds.append(progress)
    return {"all_exponents_positive_before_power_use": True,
            "power_bases_proved_positive": len(power), "rounds": rounds}


def digit_controls():
    cases = 0
    for uppers in [(1, 1), (1, 3), (2, 4, 1), (0, 0), (6, 3, 2)]:
        q = 2**sum(uppers) + 1
        for n in uppers:
            for k in range(0, n+3):
                numerator = (q+1)**n
                denominator = q**k
                quotient, remainder = divmod(numerator, denominator)
                digit = quotient % q
                expected = comb(n, k) if k <= n else 0
                require(digit == expected and remainder < denominator and digit < q,
                        "common-radix digit fixture")
                cases += 1
    # Deliberately undersized q=2 produces a carry: C(4,2)=6, but digit2=0.
    require(((2+1)**4 // 2**2) % 2 != comb(4, 2), "small-radix negative control")
    return {"exact_digit_cases": cases, "undersized_radix_rejected": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    eq = json.loads((args.directory / "equation.json").read_text())
    expanded = json.loads((args.directory / "expanded_polynomial.json").read_text())
    raw = json.loads((args.directory / "construction_trace.json").read_text())
    trace = Trace(raw)
    result = {"status": "PASS", "metrics": count_and_expand(eq, expanded),
              "affine_projection": replay_affine_projection(trace, eq),
              "common_radix": audit_radix(trace), "offset": audit_offsets(trace),
              "frame": audit_frame(trace), "positivity": positivity(trace),
              "digit_controls": digit_controls(),
              "hashes": {name: sha256((args.directory / name).read_bytes()).hexdigest()
                         for name in ("equation.json", "expanded_polynomial.json", "construction_trace.json")},
              "scope": "finite exact rows, polynomial expansion and stated arithmetic controls; not a proof of Con(ZFC)"}
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload)


if __name__ == "__main__":
    main()
