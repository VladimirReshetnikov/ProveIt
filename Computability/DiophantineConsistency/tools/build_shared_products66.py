#!/usr/bin/env python3
"""Reduce H2082 by three gates, with independently checked local identities.

No Lean compiler is called. The receipt is an ordinary exact ring-identity
certificate plus a structural remap, rather than a probabilistic identity
test. Modular evaluations are additional transcription diagnostics only.
"""
import argparse
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path

from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "candidates/gap2082-compact54"
DEST = ROOT / "candidates/gap2082-shared-products"
PINS = {
    "positive": "7a34fddb23453755a26c9185f3540d99bc7697848e037fecbaa20fc2df7631a9",
    "natural": "be7d9e1285a1cf674978058c3b1be2f27a17af9c0d0bdc6e4f8310481a40d001",
}
OPS = {"add", "sub", "mul"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2) + "\n").encode()


def transform(parent, degree=1845940,
              fixed_binding="../gap2082-compact54/fixed/BINDING.json"):
    """Build with CSE; leave every input and every coefficient unchanged."""
    old = parent["nodes"]
    n = parent["named_nodes"]
    r = old[n["R"]]
    require(r["kind"] == "sub" and old[r["right"]] == dict(kind="literal", value=1),
            "rank is rankPlusOne minus one")
    rank_plus_one = r["left"]
    # The parent computes (R+1) as a separate gate inside K.
    plus_gate = next(i for i, v in enumerate(old) if v["kind"] == "add"
                     and {v["left"], v["right"]} == {n["R"], r["right"]})
    replacements = {
        n["P"]: "2*M*(M*U)",
        n["A"]: "M+M*U",
        n["E"]: "k*(C*D)",
        plus_gate: "rankPlusOne",
    }
    cutsets = {
        n["P"]: [n["M"], n["U"]],
        n["A"]: [n["M"], n["U"]],
        n["E"]: [n["k"], n["C"], n["D"]],
        plus_gate: [rank_plus_one],
    }
    nodes, memo, mapping = [], {}, {}

    def emit(node):
        node = dict(node)
        if node["kind"] in ("add", "mul") and node["left"] > node["right"]:
            node["left"], node["right"] = node["right"], node["left"]
        key = tuple(sorted(node.items()))
        if key not in memo:
            memo[key] = len(nodes)
            nodes.append(node)
        return memo[key]

    def binary(kind, a, b):
        return emit(dict(kind=kind, left=a, right=b))

    def visit(index):
        if index in mapping:
            return mapping[index]
        if index == n["P"]:
            M, U = visit(n["M"]), visit(n["U"])
            result = binary("mul", emit(dict(kind="literal", value=2)),
                            binary("mul", M, binary("mul", M, U)))
        elif index == n["A"]:
            M, U = visit(n["M"]), visit(n["U"])
            result = binary("add", M, binary("mul", M, U))
        elif index == n["E"]:
            result = binary("mul", visit(n["k"]), binary("mul", visit(n["C"]), visit(n["D"])))
        elif index == plus_gate:
            result = visit(rank_plus_one)
        else:
            node = dict(old[index])
            if node["kind"] in OPS:
                node.update(left=visit(node["left"]), right=visit(node["right"]))
            result = emit(node)
        mapping[index] = result
        return result

    output = visit(parent["output"])
    names = {name: visit(index) for name, index in n.items()}
    counts = collections.Counter(v["kind"] for v in nodes if v["kind"] in OPS)
    result = copy.deepcopy(parent)
    result.update(nodes=nodes, output=output, named_nodes=names,
                  operation_counts=dict(sorted(counts.items())), total_operations=sum(counts.values()),
                  exact_degree=degree, fixed_binding=fixed_binding,
                  algebraic_rewrite="shared M*U, shared C*D, cancellation of (R+1)")
    cert = dict(retained_remap={str(k): v for k, v in sorted(mapping.items())},
                replacements=[dict(old_node=i, new_node=mapping[i],
                                   cutset=cutsets[i], expression=replacements[i])
                              for i in sorted(replacements)])
    return result, cert


def normalize(nodes, root, cuts):
    """Small sparse Z-polynomial in cut-point atoms; independent of builder.

    Monomials are sorted tuples of atom indices, so this uses just exact
    integer arithmetic and distributivity. Traversal must stop at all
    nonliteral inputs; a certificate cannot hide a new coefficient/input.
    """
    cache, used = {}, set()

    def walk(index):
        if index in cache:
            return cache[index]
        used.add(index)
        if index in cuts:
            value = {(cuts[index],): 1}
        else:
            node = nodes[index]
            kind = node["kind"]
            if kind == "literal":
                value = {(): node["value"]} if node["value"] else {}
            else:
                require(kind in OPS, "identity introduced a non-cut input")
                a, b = walk(node["left"]), walk(node["right"])
                value = collections.defaultdict(int)
                if kind == "mul":
                    for u, c in a.items():
                        for v, d in b.items():
                            value[tuple(sorted(u+v))] += c*d
                else:
                    for u, c in a.items():
                        value[u] += c
                    for u, c in b.items():
                        value[u] += (-c if kind == "sub" else c)
                value = {u: c for u, c in value.items() if c}
        cache[index] = value
        return value

    return walk(root), used


def verify(parent, child, certificate):
    """Prove equality by four local ring identities and unchanged gate rules."""
    mapping = {int(k): v for k, v in certificate["retained_remap"].items()}
    replacements = {v["old_node"]: v for v in certificate["replacements"]}
    require(len(replacements) == 4, "four independently checked local rewrites")
    covered, identities = set(), []
    for index, mapped in mapping.items():
        if index in replacements:
            entry = replacements[index]
            cuts = entry["cutset"]
            require(entry["new_node"] == mapped and all(i < index for i in cuts),
                    "identity depends only on earlier original values")
            require(len({mapping[i] for i in cuts}) == len(cuts), "distinct cut-point atoms")
            old_poly, _ = normalize(parent["nodes"], index, {v: v for v in cuts})
            new_poly, visited = normalize(child["nodes"], mapped, {mapping[v]: v for v in cuts})
            require(old_poly == new_poly, "exact local Z-polynomial identity")
            covered.update(visited)
            identities.append(dict(old_node=index, new_node=mapped, monomials=len(old_poly)))
        else:
            old = dict(parent["nodes"][index])
            if old["kind"] in OPS:
                require(old["left"] in mapping and old["right"] in mapping, "closed retained dependencies")
                old.update(left=mapping[old["left"]], right=mapping[old["right"]])
                if old["kind"] in ("add", "mul") and old["left"] > old["right"]:
                    old["left"], old["right"] = old["right"], old["left"]
            require(child["nodes"][mapped] == old, "unchanged gate after operand remap")
            covered.add(mapped)
    require(covered == set(range(len(child["nodes"]))), "every new node justified")
    require(parent["output"] in mapping and child["output"] == mapping[parent["output"]], "same output")
    require(child["named_nodes"] == {k: mapping[v] for k, v in parent["named_nodes"].items()}, "named values preserved")
    for key in ("variables", "domain", "coefficient_recipes", "source_sha256", "layout_sha256"):
        require(parent[key] == child[key], "same variables/domain/coefficients/source")
    return identities


def evaluate(body, variables, fixed, modulus):
    values = []
    for node in body["nodes"]:
        kind = node["kind"]
        if kind == "variable":
            value = variables[node["name"]]
        elif kind == "fixed":
            value = fixed[node["name"]]
        elif kind == "literal":
            value = node["value"]
        elif kind == "add":
            value = values[node["left"]]+values[node["right"]]
        elif kind == "sub":
            value = values[node["left"]]-values[node["right"]]
        else:
            require(kind == "mul", "only binary ring operations")
            value = values[node["left"]]*values[node["right"]]
        values.append(value % modulus)
    return values


def rejects_mutation(parent, child, certificate):
    bad = copy.deepcopy(child)
    # An operation-count preserving corruption of an actual changed gate.
    entry = next(v for v in certificate["replacements"] if v["expression"] == "M+M*U")
    bad["nodes"][entry["new_node"]]["kind"] = "sub"
    try:
        verify(parent, bad, certificate)
    except ValueError:
        return True
    raise ValueError("local identity corruption escaped the independent check")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="reproduce without writing")
    args = parser.parse_args()
    binding_raw = (PARENT / "fixed/BINDING.json").read_bytes()
    fixed = {}
    for entry in json.loads(binding_raw)["records"]:
        compressed = (PARENT / entry["path"]).read_bytes()
        require(sha(compressed) == entry["gzip_sha256"], "fixed gzip pin")
        raw = gzip.decompress(compressed)
        require(sha(raw) == entry["raw_sha256"], "fixed integer pin")
        fixed[entry["name"]] = entry["sign"]*int.from_bytes(raw, "little")
    files, rows = {}, []
    for domain, operations in (("positive", 440), ("natural", 447)):
        raw = (PARENT / "generated" / f"gap2082_{domain}.json").read_bytes()
        require(sha(raw) == PINS[domain], "pinned parent circuit")
        parent = json.loads(raw)
        child, certificate = transform(parent)
        identities = verify(parent, child, certificate)
        require(child["total_operations"] == operations, "three-gate saving")
        require(rejects_mutation(parent, child, certificate), "corruption rejection")
        comparisons = 0
        for modulus in (65537, 1000000007, 2147483647):
            for seed in range(20):
                # Include zero and negative diagnostics: exact identities have
                # no positivity premise, although endpoint domains are retained.
                variables = {v: seed*(j+3)-17 for j, v in enumerate(child["variables"])}
                before, after = evaluate(parent, variables, fixed, modulus), evaluate(child, variables, fixed, modulus)
                for name, i in parent["named_nodes"].items():
                    require(before[i] == after[child["named_nodes"][name]], "actual-coefficient named-value diagnostic")
                    comparisons += 1
                require(before[parent["output"]] == after[child["output"]], "actual-coefficient output diagnostic")
        circuit_raw = encoded(child)
        certificate.update(parent_sha256=sha(raw), child_sha256=sha(circuit_raw),
                           fixed_binding_sha256=sha(binding_raw), identities=identities,
                           modular_assignments=60, named_value_comparisons=comparisons,
                           corruption_control="changed A=M+M*U to subtraction; rejected",
                           scope="Exact commutative-ring equality by local normal forms and structural induction. No Lean work.")
        files[f"gap2082_{domain}.json"] = circuit_raw
        files[f"{domain}_rewrite.json"] = encoded(certificate)
        rows.append(dict(domain=domain, variables=9, operations=operations, removed_operations=3,
                         exact_degree=1845940, sha256=sha(circuit_raw)))
    files["REVIEW.json"] = encoded(dict(status="PASS", circuits=rows,
        degree_reason="Identical polynomial to pinned parent; its ordinary exact-degree certificate transfers.",
        fixed_binding_sha256=sha(binding_raw),
        scope="Size reduction only. Source/native/compiler/internal-ZFC status is inherited without strengthening."))
    files["MANIFEST.json"] = encoded({name: sha(raw) for name, raw in sorted(files.items())})
    for name, raw in files.items():
        target = DEST / name
        if args.check:
            require(target.read_bytes() == raw, f"reproduce {name}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
    for domain, operations in (("positive", 440), ("natural", 447)):
        audit((f"../candidates/gap2082-shared-products/gap2082_{domain}.json",
               9, "+" if domain == "positive" else "N", 1845940, operations))
    print(json.dumps(dict(status="PASS", circuits=rows, files=len(files)), indent=2))


if __name__ == "__main__":
    main()
