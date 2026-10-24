#!/usr/bin/env python3
"""Save one gate in each complete two-root norm, by an exact ring identity.

No Lean or historical emitter is executed. All parents remain immutable.
"""
import argparse
import collections
import copy
import gzip
import json
from pathlib import Path

from build_radical_d_shared import DAG
from build_shared_products66 import encoded, evaluate, normalize, sha
from build_shared_products71 import PORTS, fixed_values
from review_proposal_frontier import require

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "candidates/norm-tail-sharing"
OPS = {"add", "sub", "mul"}


def cuts(parent):
    """Recognize (t²-s(a+b))²-4s²ab; equality is checked independently."""
    nodes = parent["nodes"]
    output = nodes[parent["output"]]
    require(output["kind"] == "sub", "norm subtraction")
    outer = nodes[output["left"]]
    require(outer["kind"] == "mul" and outer["left"] == outer["right"], "outer square")
    inner = nodes[outer["left"]]
    require(inner["kind"] == "sub", "inner difference")
    square, product = nodes[inner["left"]], nodes[inner["right"]]
    require(square["kind"] == "mul" and square["left"] == square["right"], "center square")
    require(product["kind"] == "mul", "scale times radicand sum")
    terms = [i for i in (product["left"], product["right"]) if nodes[i]["kind"] == "add"]
    require(len(terms) == 1, "unique radicand sum")
    total = terms[0]
    scale = next(i for i in (product["left"], product["right"]) if i != total)
    result = [square["left"], scale, nodes[total]["left"], nodes[total]["right"]]
    require(len(set(result)) == 4, "distinct identity atoms")
    return result


def transform(parent, case):
    d, mapping = DAG(), {}

    def visit(i):
        if i not in mapping:
            node = dict(parent["nodes"][i])
            if node["kind"] in OPS:
                node.update(left=visit(node["left"]), right=visit(node["right"]))
            mapping[i] = d.emit(node)
        return mapping[i]

    cut = cuts(parent)
    t, s, a, b = [visit(i) for i in cut]
    op = d.binary
    u = op("mul", t, t)
    inner = op("add", u, op("mul", s, op("sub", a, b)))
    cross = op("mul", op("mul", op("mul", d.literal(4), s), a), u)
    output = op("sub", op("mul", inner, inner), cross)
    counts = collections.Counter(n["kind"] for n in d.nodes if n["kind"] in OPS)
    child = copy.deepcopy(parent)
    child.update(nodes=d.nodes, output=output,
        named_nodes={name: mapping[i] for name, i in parent["named_nodes"].items() if i in mapping},
        total_operations=sum(counts.values()), operation_counts=dict(sorted(counts.items())),
        exact_degree=case["degree"], fixed_binding=case["fixed_binding"],
        algebraic_rewrite="(t²-s(a+b))²-4s²ab = (t²+s(a-b))²-4sat²")
    child["parent_research_relative"] = case["parent"]
    for key in ("predecessor", "source_files"):
        if key in child:
            child["inherited_"+key] = child.pop(key)
    if "fixed_coefficients" in child:
        child["fixed_coefficients"] = case["fixed_binding"]
    child["named_nodes"].update(norm_squared_center=u, norm_alternate_inner=inner, norm_output=output)
    degrees = []
    for node in d.nodes:
        kind = node["kind"]
        degrees.append(1 if kind == "variable" else 0 if kind not in OPS else
            degrees[node["left"]]+degrees[node["right"]] if kind == "mul" else
            max(degrees[node["left"]], degrees[node["right"]]))
    child["degree_upper_bound"] = degrees[output]
    child["named_degree_bounds"] = {k: degrees[i] for k, i in child["named_nodes"].items()}
    return child, dict(cutset=cut, retained_remap={str(k): v for k, v in sorted(mapping.items())})


def verify(parent, child, certificate):
    mapping = {int(k): v for k, v in certificate["retained_remap"].items()}
    cut = certificate["cutset"]
    old, _ = normalize(parent["nodes"], parent["output"], {i: i for i in cut})
    new, visited = normalize(child["nodes"], child["output"], {mapping[i]: i for i in cut})
    require(old == new and len(old) == 6, "complete exact six-term norm identity")
    covered = set(visited)
    for i, j in mapping.items():
        node = dict(parent["nodes"][i])
        if node["kind"] in OPS:
            require(node["left"] in mapping and node["right"] in mapping, "closed prefix")
            node.update(left=mapping[node["left"]], right=mapping[node["right"]])
            if node["kind"] in ("add", "mul") and node["left"] > node["right"]:
                node["left"], node["right"] = node["right"], node["left"]
        require(child["nodes"][j] == node, "every retained gate justified")
        covered.add(j)
    require(covered == set(range(len(child["nodes"]))), "every child gate justified")
    live, todo = set(), [child["output"]]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        node = child["nodes"][i]
        if node["kind"] in OPS:
            require(0 <= node["left"] < i and 0 <= node["right"] < i, "DAG topology")
            todo.extend((node["left"], node["right"]))
    require(len(live) == len(child["nodes"]), "all nodes live")
    require({n["name"] for n in child["nodes"] if n["kind"] == "variable"} == set(parent["variables"]), "all inputs live")
    for key in ("variables", "domain", "coefficient_recipes", "fixed_recipes"):
        require(parent.get(key) == child.get(key), "same input and whole coefficient recipes")
    return len(old)


def fixed(case, parent):
    if case["fixed_kind"] == "ports31":
        binding = json.loads((PORTS / "COEFFICIENT_BINDING.json").read_text())
        return fixed_values(parent, binding)
    path = DEST / case["fixed_binding"]
    binding = json.loads(path.read_text())
    result = {}
    if case["fixed_kind"] != "norm10":
        payload_root = DEST / case["fixed_root"] if "fixed_root" in case else path.parent.parent
        for item in binding["records"]:
            compressed = (payload_root / item["path"]).read_bytes()
            raw = gzip.decompress(compressed)
            require(sha(compressed) == item["gzip_sha256"] and sha(raw) == item["raw_sha256"], "whole shared leaf hashes")
            result[item["name"]] = item["sign"] * int.from_bytes(raw, "little")
    else:
        for name, item in binding.items():
            compressed = (path.parent / item["file"]).read_bytes()
            raw = gzip.decompress(compressed)
            require(sha(compressed) == item["gzip_sha256"] and sha(raw) == item["raw_sha256"], "whole norm10 leaf hashes")
            require(raw[0] in (0, 1), "signed magnitude tag")
            result[name] = (-1 if raw[0] else 1) * int.from_bytes(raw[1:], "little")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files, receipts = {}, []
    for case in json.loads((DEST / "PARENTS.json").read_text()):
        raw = (ROOT / case["parent"]).read_bytes()
        require(sha(raw) == case["parent_sha256"], "immutable parent bytes")
        parent = json.loads(raw)
        require(parent["total_operations"] == case["operations"], "parent count")
        child, certificate = transform(parent, case)
        monomials = verify(parent, child, certificate)
        require(child["total_operations"] == case["operations"]-1, "exactly one gate saved")
        bad = copy.deepcopy(child)
        bad["nodes"][bad["output"]]["kind"] = "add"
        try:
            verify(parent, bad, certificate)
        except ValueError:
            pass
        else:
            raise ValueError("corruption accepted")
        actual = fixed(case, parent)
        for modulus in (65537, 1000000007, 2147483647):
            for seed in range(20):
                values = {v: seed*(j+3)-17 for j, v in enumerate(child["variables"])}
                before, after = evaluate(parent, values, actual, modulus), evaluate(child, values, actual, modulus)
                require(before[parent["output"]] == after[child["output"]], "actual-coefficient output diagnostic")
                for i, j in ((int(i), j) for i, j in certificate["retained_remap"].items()):
                    require(before[i] == after[j], "actual-coefficient prefix diagnostic")
        certificate.update(parent=case["parent"], parent_sha256=sha(raw), child_sha256=sha(encoded(child)))
        files[case["name"]+".json"] = encoded(child)
        files[case["name"]+"_identity.json"] = encoded(certificate)
        receipts.append(dict(name=case["name"], variables=len(child["variables"]), domain=child["domain"],
            parent_operations=case["operations"], operations=child["total_operations"], exact_degree=case["degree"],
            exact_identity_monomials=monomials, modular_assignments=60, fixed_leaves=len(actual),
            all_nodes_live=True, corruption_rejected=True, output_polynomial_identical=True))
    files["REVIEW.json"] = encoded(dict(status="PASS", cases=receipts,
        scope="Exact ring identity plus complete prefix remap. Parent ordinary semantics and exact degree inherited; no Lean/internal-ZFC certificate."))
    files["MANIFEST.json"] = encoded({k: sha(v) for k, v in sorted(files.items())})
    for name, raw in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == raw, "deterministically reproduce "+name)
        else:
            path.write_bytes(raw)
    print(files["REVIEW.json"].decode(), end="")


if __name__ == "__main__":
    main()
