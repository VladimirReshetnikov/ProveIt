#!/usr/bin/env python3
"""Combine the471-gate short guard with the compact earlier coordinate shears."""
import argparse
import collections
import copy
import json
from pathlib import Path

from build_radical_d_shared import DAG
from build_shared_products66 import encoded, evaluate, normalize, sha
from build_norm_tail_sharing import fixed
from review_proposal_frontier import require

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "candidates/short-guard-shears"
OLD = ROOT / "candidates/norm-tail-sharing/source10"
CASES = {
    "linear": (["A", "E", "G", "H"], 475, 1179788),
    "cubic": (["A", "E0", "D", "C", "G", "H"], 478, 1114252),
    "sixterm": (["halfA", "B1", "C", "xi", "y"], 512, 1080888),
}
OPS = {"add", "sub", "mul"}


def named(body, key):
    if key != "y":
        return body["named_nodes"][key]
    return next(i for i, n in enumerate(body["nodes"]) if n == dict(kind="variable", name="y"))


def construct(parent, old, keys):
    d, mapping, roots = DAG(), {}, {}
    cuts = {named(old, key): named(parent, key) for key in keys}

    def root(i):
        if i not in roots:
            if i in cuts:
                roots[i] = visit(cuts[i])
            else:
                node = dict(old["nodes"][i])
                if node["kind"] in OPS:
                    node.update(left=root(node["left"]), right=root(node["right"]))
                else:
                    require(node["kind"] == "literal", "shear uses only specified earlier cuts")
                roots[i] = d.emit(node)
        return roots[i]

    def visit(i):
        if i not in mapping:
            node = dict(parent["nodes"][i])
            if node == dict(kind="variable", name="m"):
                result = d.binary("add", d.emit(node), root(old["named_nodes"]["shear"]))
            else:
                if node["kind"] in OPS:
                    node.update(left=visit(node["left"]), right=visit(node["right"]))
                result = d.emit(node)
            mapping[i] = result
        return mapping[i]

    output = visit(parent["output"])
    child = copy.deepcopy(parent)
    counts = collections.Counter(n["kind"] for n in d.nodes if n["kind"] in OPS)
    child.update(nodes=d.nodes, output=output, named_nodes={k: mapping[i] for k, i in parent["named_nodes"].items()},
        operation_counts=dict(sorted(counts.items())), total_operations=sum(counts.values()),
        fixed_coefficients="../norm-tail-sharing/source10/FIXED_COEFFICIENTS.json",
        fixed_binding="../norm-tail-sharing/source10/FIXED_COEFFICIENTS.json",
        polynomial_identity="P_new(v,m)=P_short_guard(v,m+R(v))", inverse="m=m_old-R(v)")
    child["named_nodes"]["shear"] = roots[old["named_nodes"]["shear"]]
    child["inherited_source_files"] = child.pop("source_files")
    degrees = []
    for n in d.nodes:
        degrees.append(1 if n["kind"] == "variable" else 0 if n["kind"] not in OPS else
            degrees[n["left"]]+degrees[n["right"]] if n["kind"] == "mul" else max(degrees[n["left"]], degrees[n["right"]]))
    child["degree_upper_bound"] = degrees[output]
    child["named_degree_bounds"] = {k: degrees[i] for k, i in child["named_nodes"].items()}
    certificate = dict(retained_remap={str(k): v for k, v in sorted(mapping.items())},
        old_shear=old["named_nodes"]["shear"], new_shear=child["named_nodes"]["shear"],
        cuts={str(i): mapping[j] for i, j in cuts.items()})
    return child, certificate


def verify(parent, old, child, cert):
    mapping = {int(k): v for k, v in cert["retained_remap"].items()}
    cuts = {int(k): v for k, v in cert["cuts"].items()}
    a, _ = normalize(old["nodes"], cert["old_shear"], {i: i for i in cuts})
    b, covered = normalize(child["nodes"], cert["new_shear"], {j: i for i, j in cuts.items()})
    require(a == b, "exact shear polynomial in the stated earlier registers")
    for i, j in mapping.items():
        node = dict(parent["nodes"][i])
        if node == dict(kind="variable", name="m"):
            actual = child["nodes"][j]
            require(actual["kind"] == "add" and cert["new_shear"] in (actual["left"], actual["right"]), "translated last coordinate")
            other = actual["left"] if actual["right"] == cert["new_shear"] else actual["right"]
            require(child["nodes"][other] == node, "free unchanged integer m")
            covered.add(other)
        else:
            if node["kind"] in OPS:
                node.update(left=mapping[node["left"]], right=mapping[node["right"]])
                if node["kind"] in ("add", "mul") and node["left"] > node["right"]:
                    node["left"], node["right"] = node["right"], node["left"]
            require(child["nodes"][j] == node, "complete parent substitution by gate induction")
        covered.add(j)
    require(covered == set(range(len(child["nodes"]))), "all child gates justified")
    require(child["output"] == mapping[parent["output"]], "same translated output")
    require(child["domain"] == "Z" and child["variables"] == parent["variables"], "same ten unrestricted inputs")
    seen, todo = set(), [cert["new_shear"]]
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        node = child["nodes"][i]
        require(node != dict(kind="variable", name="m"), "shear independent of the translated coordinate")
        if node["kind"] in OPS:
            todo.extend((node["left"], node["right"]))
    return len(a)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    pins = json.loads((DEST / "SOURCE_PINS.json").read_text())
    for name, record in pins["files"].items():
        require(sha((DEST / "source" / name).read_bytes()) == record["sha256"], "immutable new source")
    parent = json.loads((DEST / "source/parent471.json").read_text())
    require(parent["total_operations"] == 471, "short-guard parent cost")
    binding = ROOT / "candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json"
    require(sha(binding.read_bytes()) == pins["shared_fixed_manifest_sha256"], "identical whole fixed binding")
    actual = fixed(dict(fixed_kind="norm10", fixed_binding="source10/FIXED_COEFFICIENTS.json"), parent)
    oldpins = json.loads((OLD / "SOURCE_PINS.json").read_text())
    files, receipts = {}, []
    for variant, (keys, count, degree) in CASES.items():
        raw = (OLD / ("parent_"+variant+".json")).read_bytes()
        require(sha(raw) == oldpins["parents"][variant]["sha256"], "immutable old compact shear")
        old = json.loads(raw)
        require(old["fixed_recipes"] == parent["fixed_recipes"], "whole coefficient recipes unchanged")
        child, cert = construct(parent, old, keys)
        require(child["total_operations"] == count, "live operation count")
        terms = verify(parent, old, child, cert)
        bad = copy.deepcopy(child)
        bad["nodes"][bad["output"]]["kind"] = "add"
        try:
            verify(parent, old, bad, cert)
        except ValueError:
            pass
        else:
            raise ValueError("changed norm output was accepted")
        live, todo = set(), [child["output"]]
        while todo:
            i = todo.pop()
            if i in live:
                continue
            live.add(i)
            node = child["nodes"][i]
            if node["kind"] in OPS:
                require(0 <= node["left"] < i and 0 <= node["right"] < i, "topology")
                todo.extend((node["left"], node["right"]))
        require(len(live) == len(child["nodes"]), "all nodes live")
        for modulus in (65537, 1000000007, 2147483647):
            for seed in range(20):
                values = {v: seed*(j+3)-17 for j, v in enumerate(child["variables"])}
                out = evaluate(child, values, actual, modulus)
                translated = dict(values)
                translated["m"] += out[child["named_nodes"]["shear"]]
                before = evaluate(parent, translated, actual, modulus)
                require(out[child["output"]] == before[parent["output"]], "signed actual-coefficient shear control")
        child["exact_degree"] = degree
        cert.update(parent471_sha256=sha((DEST / "source/parent471.json").read_bytes()),
            old_shear_parent_sha256=sha(raw), child_sha256=sha(encoded(child)))
        files[variant+".json"] = encoded(child)
        files[variant+"_identity.json"] = encoded(cert)
        receipts.append(dict(variant=variant, variables=10, domain="Z", operations=count, exact_degree=degree,
            local_shear_monomials=terms, all_nodes_live=True, modular_assignments=60,
            exact_gate_substitution=True, shear_independent_of_m=True, corruption_rejected=True,
            interpretation="bijection to the471-operation short-guard parent"))
    files["REVIEW.json"] = encoded(dict(status="PASS", cases=receipts,
        scope="Exact shear/substitution certificates and fixed data; degree proof in README. Inherited ordinary calibration; no new Lean/internal-ZFC certificate."))
    files["MANIFEST.json"] = encoded({k: sha(v) for k, v in sorted(files.items())})
    for name, raw in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == raw, "deterministic reproduction "+name)
        else:
            path.write_bytes(raw)
    print(files["REVIEW.json"].decode(), end="")


if __name__ == "__main__":
    main()
