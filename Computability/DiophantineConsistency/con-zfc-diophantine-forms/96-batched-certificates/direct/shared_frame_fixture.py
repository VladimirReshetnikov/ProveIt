#!/usr/bin/env python3
"""Exact, deliberately small regression fixtures for the shared Pell frame.

The global growth frame is exercised on repeated exponent one. A separate
small-parameter index fixture tests distinct exponents and the pooled period.
These checks do not search for a ZFC refutation or its huge witnesses.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
import json
from math import prod
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pell(a, k, modulus=None):
    d = a*a-1
    def multiply(u, v):
        p = (u[0]*v[0]+d*u[1]*v[1], u[0]*v[1]+u[1]*v[0])
        return p if modulus is None else tuple(x % modulus for x in p)
    out, base = (1, 0), (a, 1)
    while k:
        if k & 1:
            out = multiply(out, base)
        base = multiply(base, base)
        k //= 2
    return out


def pooled_index_fixture(a, indices):
    first = {k: pell(a, k) for k in indices}
    P = prod(y for x, y in first.values())
    modulus = 4*P*P
    period = next(k for k in range(max(indices)+1, 100001)
                  if pell(a, k, modulus) == (1, 0))
    U, V = pell(a, period)
    require(U % modulus == 1 and V % modulus == 0, "matrix period fixture")
    require(V > 0 and V % (P*P) == 0, "pooled ordinate divisibility")
    factor = ((1-a)*pow(U, -1, 4*P)) % (4*P)
    B = a + U*factor
    if B <= 1:
        B += 4*P*U
    require(B >= 2 and (B-a) % U == 0 and (B-1) % (4*P) == 0,
            "shared parameter CRT")
    groups = []
    for k in indices:
        X, Y = first[k]
        S, R = pell(B, k)
        require(X*X-(a*a-1)*Y*Y == 1, "first index norm")
        require(U*U-(a*a-1)*V*V == 1, "auxiliary norm")
        require(S*S-(B*B-1)*R*R == 1, "second index norm")
        require(V % (Y*Y) == 0 and V >= Y*Y, "local squared divisibility")
        require((B-1) % (4*Y) == 0 and (S-X) % U == 0 and (R-k) % (4*Y) == 0,
                "local index congruences")
        groups.append({"k": k, "X": X, "Y": Y, "S": S, "R": R})
    return {"A": a, "P": P, "period_modulus": modulus, "period": period,
            "U": U, "V": V, "B": B, "groups": groups}


def full_frame_fixture():
    # The builder is used here only to emit a literal small fixture. Its
    # rows are then checked by a separate coefficient evaluator below.
    from build_common_radix import FrameBuilder, old
    FrameBuilder.shared_offset_enabled = True
    builder = FrameBuilder(positive_powers=True)
    inputs = [(2, 1), (3, 1)]
    outputs = [builder.power(old.const(n), old.const(k)) for n, k in inputs]
    builder.finalize_powers()
    frame = builder.shared_frame_log
    names = {v["name"]: i for i, v in enumerate(builder.variables)}
    assigned = {out[1]: n**k for out, (n, k) in zip(outputs, inputs)}
    W = 1+sum(n+k+n**k for n, k in inputs)
    A, WZ = pell(W+1, W)
    require(WZ % W == 0, "last norm divisibility")
    Z = WZ//W
    index = pooled_index_fixture(A, sorted({k for n, k in inputs}))
    U, V, B, P = [index[key] for key in ("U", "V", "B", "P")]
    assigned.update({names["frame.A_minus_two"]: A-2,
                     names["frame.Z"]: Z, names["frame.U"]: U,
                     names["frame.V_quotient_minus_one"]: V//(P*P)-1,
                     names["frame.B_quotient_minus_one"]: (B-1)//(4*P)-1})
    by_index = {g["k"]: g for g in index["groups"]}
    for group in frame["index_groups"]:
        k = group["k"][1]
        g = by_index[k]
        tag = group["tag"]
        assigned.update({names[tag+".X"]: g["X"],
                         names[tag+".Y_minus_index"]: g["Y"]-k,
                         names[tag+".S"]: g["S"], names[tag+".R"]: g["R"]})
    for j, (n, k) in enumerate(inputs):
        assigned[names[f"pow{j}.T"]] = 2*A*n-n*n-1
    definitions = {}
    for row in builder.rows:
        i = row["gate"]
        if i is not None:
            definitions[i] = [(c, m) for c, m in row["terms"] if m != [i]]
    def evaluator(seeds):
        @lru_cache(None)
        def value(i):
            if i in seeds:
                return seeds[i]
            return -sum(c*prod(value(j) for j in mon) for c, mon in definitions[i])
        def atom(a):
            return a[1] if a[0] == "c" else value(a[1])
        return value, atom
    _, eval_atom = evaluator(assigned)
    differences = []
    for congruence in builder.congruence_log:
        left, right, modulus = [eval_atom(congruence[key]) for key in ("left", "right", "modulus")]
        require(modulus > 0 and (right-left) % modulus == 0, "fixture congruence")
        differences.append((right-left)//modulus)
    Q = max([0] + [-d for d in differences])
    assigned[builder.shared_offset[1]] = Q
    for c, d in zip(builder.congruence_log, differences):
        assigned[c["quotient"][1]] = Q+d
    value, _ = evaluator(assigned)
    values = [value(i) for i in range(len(builder.variables))]
    require(all(x >= 0 for x in values), "negative fixture witness")
    residuals = [sum(c*prod(values[j] for j in mon) for c, mon in r["terms"])
                 for r in builder.rows]
    require(not any(residuals), "literal shared-frame fixture fails")
    bad = dict(assigned)
    bad[outputs[0][1]] += 1
    bad_value, _ = evaluator(bad)
    bad_values = [bad_value(i) for i in range(len(builder.variables))]
    bad_residuals = [sum(c*prod(bad_values[j] for j in mon) for c, mon in r["terms"])
                     for r in builder.rows]
    require(any(bad_residuals), "mutated output escaped literal rows")
    return {"inputs": inputs, "W": W, "A": A, "Z": Z,
            "index_fixture": index, "variables": builder.variables,
            "rows": builder.rows, "values": values,
            "power_outputs": outputs,
            "mutated_output_rejected": True,
            "max_witness_decimal_digits": max(len(str(x)) for x in values)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    full = full_frame_fixture()
    distinct = pooled_index_fixture(2, [1, 2])
    result = {"status": "PASS", "full_shared_frame": full,
              "distinct_index_frame": distinct,
              "scope": "small exact regression controls; no search for a consistency witness"}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": "PASS", "full_frame_variables": len(full["variables"]),
                      "full_frame_rows": len(full["rows"]),
                      "full_frame_max_witness_digits": full["max_witness_decimal_digits"],
                      "distinct_index_period": distinct["period"]}, indent=2))


if __name__ == "__main__":
    main()
