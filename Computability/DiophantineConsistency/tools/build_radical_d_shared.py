#!/usr/bin/env python3
"""Replace 654 expanded radical terms by312 in the already computed D.

The output polynomial is identical to the pinned arriving parent. Exact
local polynomial normalization proves the replacement and a complete
retained-gate remap proves the whole circuit identity. No Lean is run.
"""
import argparse
import collections
import copy
import functools
import json
from pathlib import Path

from build_shared_products66 import (encoded, evaluate, normalize, sha,
    transform as share_products, verify as verify_products)
from build_shared_products71 import fixed_values, PORTS, BINDING
from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "candidates/radical-d-shared"
PINS = {
    "parent.json": "b7dae3927040c428146e0b7d2c2cb7590c99f1915a5b14c5471cb92ea4d5594c",
    "radical.json": "e268598e0443868226c944bb10fad9f31bb9d335312ae0d6d3e2a61b577294d9",
}
OPS = {"add", "sub", "mul"}
ORDER = (4, 3, 1, 2, 0)  # Z, i, C, D, A


def reduce_table(table):
    # A^2 C^2 = D+C^2-1. Each step lowers the A exponent, hence terminates.
    @functools.lru_cache(None)
    def monomial(a, c):
        if a < 2 or c < 2:
            return {(a, c, 0): 1}
        result = collections.defaultdict(int)
        for (x, y, d), v in monomial(a-2, c-2).items():
            result[x, y, d+1] += v
            result[x, y+2, d] += v
            result[x, y, d] -= v
        return {e: v for e, v in result.items() if v}

    result = collections.defaultdict(int)
    for e, v in table:
        for (a, c, d), w in monomial(e[0], e[1]).items():
            result[a, c, d, e[2], e[3]] += int(v)*w
    return {e: v for e, v in result.items() if v}


class DAG:
    def __init__(self):
        self.nodes, self.memo = [], {}

    def emit(self, node):
        node = dict(node)
        k = node["kind"]
        if k in ("add", "mul") and node["left"] > node["right"]:
            node["left"], node["right"] = node["right"], node["left"]
        key = tuple(sorted(node.items()))
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append(node)
        return self.memo[key]

    def literal(self, value):
        return self.emit(dict(kind="literal", value=value))

    def binary(self, kind, a, b):
        if kind == "mul":
            if self.nodes[a] == dict(kind="literal", value=1):
                return b
            if self.nodes[b] == dict(kind="literal", value=1):
                return a
        return self.emit(dict(kind=kind, left=a, right=b))

    def power(self, value, exponent):
        if exponent == 0:
            return self.literal(1)
        if exponent == 1:
            return value
        half = self.power(value, exponent//2)
        square = self.binary("mul", half, half)
        return self.binary("mul", square, value) if exponent % 2 else square


def transform(parent, table):
    dag, mapping = DAG(), {}
    names = parent["named_nodes"]
    i_node = next(i for i, n in enumerate(parent["nodes"]) if n == dict(kind="variable", name="i"))
    cuts = [names["A"], names["C"], names["D"], i_node, names["Z"]]

    def visit(index):
        if index in mapping:
            return mapping[index]
        if index == names["Pstar"]:
            values = [visit(v) for v in cuts]

            @functools.lru_cache(None)
            def horner(items):
                poly = dict(items)
                if all(not any(e) for e in poly):
                    return dag.literal(sum(poly.values()))
                common = tuple(min(e[j] for e in poly) for j in range(5))
                if any(common):
                    rest = {tuple(e[j]-common[j] for j in range(5)): v for e, v in poly.items()}
                    result = horner(tuple(sorted(rest.items())))
                    for j, exponent in enumerate(common):
                        if exponent:
                            result = dag.binary("mul", result, dag.power(values[j], exponent))
                    return result
                j = next(j for j in ORDER if any(e[j] for e in poly))
                groups = collections.defaultdict(dict)
                for e, v in poly.items():
                    ee = list(e)
                    exponent, ee[j] = ee[j], 0
                    groups[exponent][tuple(ee)] = v
                exponent = max(groups)
                result = horner(tuple(sorted(groups.pop(exponent).items())))
                for next_exponent in sorted(groups, reverse=True):
                    result = dag.binary("add",
                        dag.binary("mul", result, dag.power(values[j], exponent-next_exponent)),
                        horner(tuple(sorted(groups[next_exponent].items()))))
                    exponent = next_exponent
                return dag.binary("mul", result, dag.power(values[j], exponent))

            result = horner(tuple(sorted(table.items())))
        else:
            node = dict(parent["nodes"][index])
            if node["kind"] in OPS:
                node.update(left=visit(node["left"]), right=visit(node["right"]))
            result = dag.emit(node)
        mapping[index] = result
        return result

    output = visit(parent["output"])
    # Values not needed by the new polynomial are not extra circuit outputs.
    # Existing useful named values are nevertheless preserved below.
    new_names = {name: mapping[v] for name, v in names.items() if v in mapping}
    child = copy.deepcopy(parent)
    counts = collections.Counter(n["kind"] for n in dag.nodes if n["kind"] in OPS)
    child.update(nodes=dag.nodes, output=output, named_nodes=new_names,
                 total_operations=sum(counts.values()), operation_counts=dict(sorted(counts.items())),
                 majorant_encoding="312-term D-reduced Horner polynomial", majorant_order=list(ORDER))
    certificate = dict(retained_remap={str(k): v for k, v in sorted(mapping.items())},
                       old_majorant=names["Pstar"], new_majorant=mapping[names["Pstar"]], cutset=cuts)
    return child, certificate


def multiply(a, b):
    result = collections.defaultdict(int)
    for u, c in a.items():
        for v, d in b.items():
            result[tuple(sorted(u+v))] += c*d
    return {u: c for u, c in result.items() if c}


def verify(parent, child, certificate):
    mapping = {int(k): v for k, v in certificate["retained_remap"].items()}
    old_root, new_root, cuts = (certificate[k] for k in ("old_majorant", "new_majorant", "cutset"))
    A, C, D, i, Z = cuts
    require(all(v < old_root for v in cuts), "earlier cut points")
    require(len(set(cuts)) == 5 and len({mapping[v] for v in cuts}) == 5,
            "distinct old and mapped cut points")
    require(new_root == mapping[old_root], "majorant correspondence")
    # Independently verify the literal parent's D relation, then expand the
    # replacement only at five atomic old values. No builder table is trusted.
    d_poly, _ = normalize(parent["nodes"], D, {A: A, C: C})
    require(d_poly == {tuple(sorted((A, A, C, C))): 1, (C, C): -1, (): 1}, "literal D relation")
    old_poly, _ = normalize(parent["nodes"], old_root, {v: v for v in cuts})
    new_poly, covered = normalize(child["nodes"], new_root, {mapping[v]: v for v in cuts})
    powers = [{(): 1}]
    for _ in range(max(m.count(D) for m in new_poly)):
        powers.append(multiply(powers[-1], d_poly))
    expanded = collections.defaultdict(int)
    for monomial, coefficient in new_poly.items():
        bare = tuple(v for v in monomial if v != D)
        for term, value in powers[monomial.count(D)].items():
            expanded[tuple(sorted(bare+term))] += coefficient*value
    require(old_poly == {e: v for e, v in expanded.items() if v}, "exact free-register radical identity")
    for index, mapped in mapping.items():
        if index == old_root:
            continue
        node = dict(parent["nodes"][index])
        if node["kind"] in OPS:
            require(node["left"] in mapping and node["right"] in mapping, "retained dependency")
            node.update(left=mapping[node["left"]], right=mapping[node["right"]])
            if node["kind"] in ("add", "mul") and node["left"] > node["right"]:
                node["left"], node["right"] = node["right"], node["left"]
        require(child["nodes"][mapped] == node, "every other gate unchanged")
        covered.add(mapped)
    require(covered == set(range(len(child["nodes"]))), "complete new-node coverage")
    require(child["output"] == mapping[parent["output"]], "output remap")
    for key in ("variables", "domain", "source_sha256", "layout_sha256", "coefficient_recipes", "exact_degree"):
        require(child[key] == parent[key], "preserved polynomial interface")
    return dict(original_monomials=len(old_poly), reduced_monomials=len(new_poly),
                expanded_monomials=sum(v != 0 for v in expanded.values()),
                scope="Exact integer polynomial identity plus retained-gate induction")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = {}
    for name, digest in PINS.items():
        raw = (DEST / "source" / name).read_bytes()
        require(sha(raw) == digest, "pinned arriving inert data")
        source[name] = json.loads(raw)
    parent = source["parent.json"]
    require(parent["total_operations"] == 1753 and parent["exact_degree"] == 1158228, "parent metrics")
    table = reduce_table(source["radical.json"]["T_terms"])
    intermediate, first = transform(parent, table)
    identity = verify(parent, intermediate, first)
    require(intermediate["total_operations"] == 1068, "D reduction gate count")
    child, second = share_products(intermediate, degree=1158228, fixed_binding=BINDING)
    second_identities = verify_products(intermediate, child, second)
    require(child["total_operations"] == 1065, "shared-products gate count")
    bad = copy.deepcopy(intermediate)
    bad["nodes"][first["new_majorant"]]["kind"] = "add"
    try:
        verify(parent, bad, first)
    except ValueError:
        pass
    else:
        raise ValueError("majorant corruption escaped exact identity check")
    binding_raw = (PORTS / "COEFFICIENT_BINDING.json").read_bytes()
    fixed = fixed_values(parent, json.loads(binding_raw))
    for modulus in (65537, 1000000007, 2147483647):
        for seed in range(20):
            values = {v: seed*(j+3)-17 for j, v in enumerate(child["variables"])}
            before, after = evaluate(parent, values, fixed, modulus), evaluate(child, values, fixed, modulus)
            require(before[parent["output"]] == after[child["output"]], "actual-coefficient output diagnostic")
            for name, mapped in child["named_nodes"].items():
                require(before[parent["named_nodes"][name]] == after[mapped], "named-value diagnostic")
    first.update(identity=identity, parent_sha256=PINS["parent.json"], child_sha256=sha(encoded(intermediate)))
    second.update(identities=second_identities, parent_sha256=sha(encoded(intermediate)), child_sha256=sha(encoded(child)))
    files = {
        "d_reduced.json": encoded(intermediate), "equation9.json": encoded(child),
        "d_rewrite.json": encoded(first), "products_rewrite.json": encoded(second),
        "reduced_table.json": encoded([[e, v] for e, v in sorted(table.items())]),
        "REVIEW.json": encoded(dict(status="PASS", variables=9, domain="strictly positive integers",
            operations=1065, parent_operations=1753, removed_operations=688, exact_degree=1158228,
            local_identity=identity, modular_assignments=60, corruption_rejected=True,
            source_pins=PINS, fixed_binding_sha256=sha(binding_raw),
            scope="Identical ring polynomial. Parent's ordinary degree/calibration boundaries are inherited; no Lean work."))}
    files["MANIFEST.json"] = encoded({name: sha(raw) for name, raw in sorted(files.items())})
    for name, raw in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == raw, f"reproduce {name}")
        else:
            path.write_bytes(raw)
    audit(("../candidates/radical-d-shared/equation9.json", 9, "+", 1158228, 1065))
    print(files["REVIEW.json"].decode(), end="")


if __name__ == "__main__":
    main()
