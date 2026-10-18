#!/usr/bin/env python3
"""Generate/check small Boolean edits to original-layout DNE mask 32.

python boolean_bundle_variants.py --generate
python boolean_bundle_variants.py --check

Every edit has a named classical implicational equivalence, a formula-position
address, and before/after subtrees.  The checker replays these independently,
checks the schema truth tables, and validates exact AX macro emission.  The
uniform common-core proof and per-macro binary bridge are separate artifacts.
"""
import argparse
import hashlib
import itertools
import json
import zlib
from pathlib import Path

import check_dne_variants as v

HERE = Path(__file__).resolve().parent
OUT = HERE / "boolean_local_variants.json"
I, N = v.imp, v.neg


def applications(t):
    if not isinstance(t, tuple) or t[0] != "imp":
        return []
    a, b = t[1:]
    result = []
    if v.is_neg(t) and v.is_neg(a):
        result.append(("double_negation", a[1]))
    if v.is_neg(a) and v.is_neg(b):
        result.append(("negative_contraposition", I(b[1], a[1])))
    if isinstance(b, tuple) and b[0] == "imp":
        result.append(("antecedent_exchange", I(b[1], I(a, b[2]))))
    if v.is_neg(a):
        result.append(("negative_antecedent_exchange", I(N(b), a[1])))
        if isinstance(a[1], tuple) and a[1][0] == "imp":
            x, y = a[1][1:]
            result.append(("unpack_negative_implication", I(x, I(N(y), b))))
    if v.is_neg(b):
        result.append(("negative_consequent_exchange", I(b[1], N(a))))
    return [(name, u) for name, u in result if u != t]


def positions(t, p=()):
    if not isinstance(t, tuple):
        return
    if t[0] == "imp":
        yield p, t
        yield from positions(t[1], p + (1,))
        yield from positions(t[2], p + (2,))
    elif t[0] == "all":
        yield from positions(t[2], p + (2,))


def at(t, p):
    for x in p:
        assert isinstance(t, tuple) and (t[0] == "imp" or (t[0] == "all" and x == 2))
        t = t[x]
    return t


def replace(t, p, u):
    if not p:
        return u
    k, a, b = t
    return (k, replace(a, p[1:], u), b) if p[0] == 1 else (k, a, replace(b, p[1:], u))


def schemas():
    a, b, c = "A", "B", "C"
    return {
        "double_negation": (N(N(a)), a),
        "negative_contraposition": (I(N(a), N(b)), I(b, a)),
        "antecedent_exchange": (I(a, I(b, c)), I(b, I(a, c))),
        "negative_antecedent_exchange": (I(N(a), b), I(N(b), a)),
        "negative_consequent_exchange": (I(a, N(b)), I(b, N(a))),
        "unpack_negative_implication": (I(N(I(a, b)), c), I(a, I(N(b), c))),
    }


def truth(t, env):
    if t == 1:
        return False
    if isinstance(t, str):
        return env[t]
    assert t[0] == "imp"
    return not truth(t[1], env) or truth(t[2], env)


def context():
    spec = v.load_spec()
    original = spec["bundle"]("a", "b", "c")
    paths = v.redexes(original)
    base = v.normalize(original, {paths[5]})
    rows = spec["ax_rows"]("a", "old_cache", "b", "c", "u")
    prefix = [166, 121, 180, 176] + [m for r in rows[1:] for m in v.emit(r)]
    mapping = json.loads((HERE / "macro_to_fine.json").read_text())
    return original, base, rows, prefix, mapping


def record(name, formula, proof, rows, prefix, mapping):
    word = prefix + v.emit(formula) + v.TAIL
    stack, reads = v.execute_macros(word[:-5])
    assert stack == ["old_top"] + rows + [formula]
    assert reads == [(176, 2), (158, 4)]
    assert formula[0] == "imp"
    fine = "".join(mapping[str(x)] for x in word)
    return {"name": name, "base_mask": 32, "rewrites": proof, "bundle": formula,
            "word": word, "fine_AX": fine, "fine_length": len(fine),
            "macro_length": len(word), "formula_tree_nodes": v.nodes(formula),
            "fine_sha256": hashlib.sha256(fine.encode()).hexdigest(),
            "zlib_bytes_heuristic_only": len(zlib.compress(fine.encode(), 9))}


def generate():
    original, base, rows, prefix, mapping = context()
    out = [record("mask32_control", base, [], rows, prefix, mapping)]
    seen = {base}
    for p, t in positions(base):
        for rule, u in applications(t):
            f = replace(base, p, u)
            if f in seen or f[0] != "imp":
                continue
            seen.add(f)
            proof = [{"rule": rule, "address": p, "before": t, "after": u}]
            out.append(record(f"mask32_local_{len(out):03d}", f, proof, rows, prefix, mapping))
    payload = {"scope": "Single Boolean edits to exact original-layout DNE mask32; no new machine count claimed.",
               "variants": out}
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def check(payload):
    for name, (a, b) in schemas().items():
        for values in itertools.product((False, True), repeat=3):
            env = dict(zip(("A", "B", "C"), values))
            assert truth(a, env) == truth(b, env), name
    original, base, rows, prefix, mapping = context()
    for row in payload["variants"]:
        f = base
        for step in row["rewrites"]:
            p = tuple(step["address"])
            old = at(f, p)
            assert old == v.freeze(step["before"])
            options = dict(applications(old))
            assert step["rule"] in schemas()
            new = options[step["rule"]]
            assert new == v.freeze(step["after"])
            f = replace(f, p, new)
        assert f == v.freeze(row["bundle"])
        exact = record(row["name"], f, row["rewrites"], rows, prefix, mapping)
        for key in ("word", "fine_AX", "fine_length", "macro_length", "formula_tree_nodes", "fine_sha256"):
            assert exact[key] == row[key], (row["name"], key)
    full = json.loads((HERE / "boolean_first_variant.json").read_text())
    f = original
    names = {"DNE": "double_negation", "contraposition": "negative_contraposition"}
    for old_name, p in full["rewrite_steps"]:
        old = at(f, tuple(p))
        new = dict(applications(old))[names[old_name]]
        f = replace(f, tuple(p), new)
    assert f == v.freeze(full["bundle"])
    exact = record(full["name"], f, [], rows, prefix, mapping)
    for key in ("word", "fine_AX", "fine_length", "macro_length", "formula_tree_nodes", "fine_sha256"):
        assert exact[key] == full[key], ("full_boolean_target", key)
    report = {"status": "PASS", "variants": len(payload["variants"]),
              "classical_schema_truth_tables": len(schemas()),
              "base_mask": 32, "all_rewrites_replayed": True,
              "all_AX_interfaces_checked": True,
              "full_1144_target_replayed": True,
              "minimum_fine_length": min(r["fine_length"] for r in payload["variants"]),
              "scope": "Finite proof-schema and symbolic emitter check; common-core and machine bridges separate."}
    (HERE / "boolean_local_checks.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = generate() if args.generate else json.loads(OUT.read_text())
    check(payload)


if __name__ == "__main__":
    main()
