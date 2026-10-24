#!/usr/bin/env python3
"""Check an exact additive gate path proving the literal beta majorant.

The finite certificate witnesses E >= D^2 and H=E+F for the actual bound
evaluation, D=1+(t+1)y. Interpreting the path uses only the natural gate
equations. H>=t additionally uses the separately checked endpoint row.
"""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def audit(directory):
    source_dir = directory/"source"
    expected = json.loads((directory/"SOURCE_PINS.json").read_text())["files"]
    for name in ["build_equation.py", "direct_calculus.py", "wire_eliminated_source.json"]:
        need(sha256((source_dir/name).read_bytes()).hexdigest() == expected[name]["candidate_sha256"],
             "source identity: "+name)
    sys.path.insert(0, str(source_dir))
    try:
        spec = importlib.util.spec_from_file_location("beta_majorant_builder", source_dir/"build_equation.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        source = json.loads((source_dir/"wire_eliminated_source.json").read_text())
        b = module.construct(source, "mixed13", positive_powers=True)
        names = {v["name"]: ("v", i) for i, v in enumerate(b.variables)}
        one = ("c", 1)
        params = {name: names[name] for name in ["x", "y", "M0"]}
        params.update(t=b.add(names["t0"], one), m=b.add(names["m0"], one))
        local_names = ["p", "q", "v", "a", "b", "c", "d", "S", "Sp", "u", "r", "vq", "rp"]
        bound = {name: params["m"] if name in ["p", "q", "v"] else names["crt.extra_bound"]
                 for name in local_names}
        before = len(b.cache)
        ep, fp = b.source_pair(source, params | bound, params["t"], False)
        H = b.add(ep, fp)
        denom = b.add(b.mul(b.add(params["t"], one), params["y"]), one)
        denom_squared = b.square(denom)
        need(len(b.cache) == before, "majorant reconstruction must reuse existing gate data")
        first_factorial = next(m for m in b.macro_log if m["macro"] == "factorial")
        need(first_factorial["n"] == H, "actual factorial argument is E+F")
        arithmetic = {output: key for key, output in b.cache.items()}
        need(arithmetic[H] == ("add", *sorted([ep, fp])), "H decomposition")
        need(arithmetic[denom_squared] == ("mul", denom, denom), "literal denominator square")

        def path(root, target, visited=None):
            if root == target:
                return []
            visited = set() if visited is None else visited
            if root in visited or root not in arithmetic:
                return None
            visited.add(root)
            op, left, right = arithmetic[root]
            if op != "add":
                return None
            for side, child, sibling in [("left", left, right), ("right", right, left)]:
                suffix = path(child, target, visited)
                if suffix is not None:
                    return [dict(output=root, operation="add", selected_side=side,
                                 selected_child=child, nonnegative_sibling=sibling)] + suffix
            return None

        certificate = path(ep, denom_squared)
        need(certificate is not None, "all-addition path from E to denominator squared")
        endpoint = [r for r in b.rows if r["label"] == "endpoint.first_remainder"]
        need(len(endpoint) == 1, "one first-remainder endpoint")
        def affine(atom):
            if atom[0] == "c":
                return {(): atom[1]}
            if atom not in arithmetic:
                return {(atom[1],): 1}
            op, left, right = arithmetic[atom]
            need(op == "add", "non-affine endpoint reconstruction")
            out = affine(left)
            for mon, c in affine(right).items():
                out[mon] = out.get(mon, 0)+c
            return out

        got = {}
        for c, mon in endpoint[0]["terms"]:
            need(len(mon) <= 1, "nonlinear raw endpoint")
            expanded = affine(("v", mon[0])) if mon else {(): 1}
            for key, a in expanded.items():
                got[key] = got.get(key, 0)+c*a
        got = {mon: c for mon, c in got.items() if c}
        wanted = {(): -2, (names["y"][1],): 1, (names["M0"][1],): -1,
                  (names["endpoint.r0"][1],): -1}
        need(got == wanted, "literal endpoint y=M0+r0+2")

        # Inspect the complete dependency cone, with no macro semantics needed.
        leaves = set()
        seen = set()

        def cone(atom):
            if atom[0] == "c":
                need(atom[1] >= 0, "negative gate constant")
            elif atom not in arithmetic:
                leaves.add(b.variables[atom[1]]["name"])
            elif atom not in seen:
                seen.add(atom)
                op, left, right = arithmetic[atom]
                need(op in ["add", "mul"], "nonmonotone bound gate")
                for child in [left, right]:
                    need(child[0] == "c" or child[1] < atom[1], "non-topological bound gate")
                    cone(child)

        cone(H)
        need(leaves == {"x", "y", "M0", "m0", "t0", "crt.extra_bound"},
             "bound must not depend on encoded columns or any power output")

        # A concrete off-source control: with y=0, H is independent of t.
        # This rejects an unconditional H>=t claim while preserving H>=1.
        def value(atom, assignment):
            memo = {}

            def evaluate(a):
                if a[0] == "c":
                    return a[1]
                if a not in arithmetic:
                    return assignment.get(b.variables[a[1]]["name"], 0)
                if a not in memo:
                    op, left, right = arithmetic[a]
                    x, y = evaluate(left), evaluate(right)
                    memo[a] = x+y if op == "add" else x*y
                return memo[a]

            return evaluate(atom)

        H0 = value(H, {})
        counter_t0 = H0
        need(H0 >= 1 and value(H, {"t0": counter_t0}) == H0 < counter_t0+1,
             "endpoint-free index-majorant negative control")
        return dict(status="PASS", factorial_argument=H,
                    E=ep, F=fp, denominator=denom, denominator_squared=denom_squared,
                    additive_majorant_path=certificate,
                    actual_endpoint_row=endpoint[0],
                    reconstructed_endpoint_terms=[[c, list(mon)] for mon, c in sorted(got.items())],
                    bound_leaves=sorted(leaves),
                    bound_arithmetic_nodes=len(seen),
                    H_positive_before_endpoint_or_power_semantics=True,
                    H_at_least_t_uses_endpoint=True,
                    global_H_at_least_t_negative_control=dict(
                        H_bits=H0.bit_length(),
                        H_sha256_little_endian=sha256(H0.to_bytes((H0.bit_length()+7)//8, "little")).hexdigest(),
                        t0="H evaluated with all free inputs zero", y=0,
                        verified="H remains constant, while t=t0+1=H+1"),
                    scope="Exact gate-path and row identities. Universal inequality proof in PROOF.md; no new C222/ZFC calibration")
    finally:
        sys.path.pop(0)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    result = audit(args.directory)
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
