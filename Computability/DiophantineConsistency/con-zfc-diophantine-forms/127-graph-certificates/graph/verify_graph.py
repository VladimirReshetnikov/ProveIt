#!/usr/bin/env python3
"""Independent verifier for the shared-graph height-one quartic compiler.

This file imports no builder. Its polynomial reconstruction expands the sum
of squares for twice P, instead of using the builder's adjacent-edge formula.
Only Python's standard library is required. Checks remain active under -O.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(target, source, scale=1):
    for mon, coefficient in source.items():
        value = target.get(mon, 0) + scale * coefficient
        if value:
            target[mon] = value
        else:
            target.pop(mon, None)


def multiply(left, right):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            mon = tuple(sorted(a + b))
            result[mon] = result.get(mon, 0) + c*d
    return {mon: c for mon, c in result.items() if c}


def sparse(terms, dimension, *, unit=False):
    result = {}
    for coefficient, indices in terms:
        require(type(coefficient) is int and coefficient != 0, "Invalid coefficient")
        require(not unit or coefficient in (-1, 1), "Non-unit normalized occurrence")
        require(all(type(i) is int and 0 <= i < dimension for i in indices), "Invalid index")
        key = tuple(sorted(indices))
        add(result, {key: coefficient})
    return result


def pullback(terms, substitutions):
    result = {}
    for coefficient, indices in terms:
        term = {(): coefficient}
        for i in indices:
            term = multiply(term, substitutions[i])
        add(result, term)
    return result


def normalization_check(source, norm):
    original_count = len(source["variables"])
    variables, rows = norm["variables"], norm["rows"]
    require(norm["original_variables"] == original_count, "Original dimension mismatch")
    require(len(variables) >= original_count, "Normalization loses original coordinates")
    substitutions, pivots, source_rows = [], set(), {}
    constants, scales = 0, 0
    for i, description in enumerate(variables):
        kind = description["kind"]
        if i < original_count:
            require(description == {"kind": "original", "source_index": i}, "Original binding")
            substitutions.append({(i,): 1})
        elif kind == "constant":
            c = description["value"]
            require(type(c) is int and c > 1, "Invalid constant descriptor")
            substitutions.append({(): c})
            constants += 1
        elif kind == "scale":
            c, v = description["coefficient"], description["variable"]
            require(type(c) is int and c > 1 and type(v) is int and 0 <= v < original_count,
                    "Invalid scale descriptor")
            substitutions.append({(v,): c})
            scales += 1
        else:
            raise ValueError("Unknown normalization variable")
    require(norm["constant_count"] == constants and norm["scale_count"] == scales,
            "Normalization counts")
    for row in rows:
        require(bool(row["terms"]) and all(len(mon) <= 2 for c, mon in row["terms"]),
                "Empty or nonquadratic normalized row")
        collected = sparse(row["terms"], len(variables), unit=True)
        image = pullback(row["terms"], substitutions)
        if row["kind"] == "source":
            r = row["source_row"]
            require(type(r) is int and 0 <= r < len(source["residuals"]) and r not in source_rows,
                    "Repeated or invalid source row")
            expected = sparse(source["residuals"][r]["terms"], original_count)
            require(image == expected, "Source-row pullback identity failed")
            source_rows[r] = row
        else:
            require(row["kind"] in ("constant", "scale"), "Unknown normalized row kind")
            require(not image, "Constructor pullback is not zero")
            all_indices = [i for c, mon in row["terms"] for i in mon]
            require(bool(all_indices), "Constructor without pivot")
            pivot = max(all_indices)
            require(pivot >= original_count and pivot not in pivots, "Constructor pivot collision")
            require(collected.get((pivot,)) == 1 and
                    all(pivot not in mon or mon == (pivot,) for mon in collected),
                    "Constructor not monic in its topological pivot")
            require(variables[pivot]["kind"] == row["kind"], "Constructor pivot kind")
            if row["kind"] == "constant":
                require(variables[pivot]["value"] == row["value"], "Constant metadata")
            else:
                require(all(variables[pivot][key] == row[key] for key in ("coefficient", "variable")),
                        "Scale metadata")
            pivots.add(pivot)
    require(pivots == set(range(original_count, len(variables))), "Missing constructor pivot")
    require(set(source_rows) == set(range(len(source["residuals"]))), "Missing source row")
    used = {i for row in rows for c, mon in row["terms"] for i in mon}
    require(used == set(range(len(variables))), "Unused normalized variable")
    return substitutions


def verify(source, artifact, certificate, source_digest):
    require(certificate["source_sha256"] == source_digest, "Source digest mismatch")
    require(artifact["schema"] == "graph-height-one-quartic-v1", "Artifact schema")
    require(certificate["schema"] == "graph-height-one-certificate-v1", "Certificate schema")
    require(artifact["domain"] == "unrestricted integers", "Domain")
    norm = certificate["normalization"]
    normalization_check(source, norm)
    final = artifact["variables"]
    dimension = len(final)
    require(dimension > 0, "Empty artifact")
    square_mode = artifact["metrics"].get("square_aliases", False)
    require(type(square_mode) is bool, "Invalid square-alias mode")
    compressed_mode = artifact["metrics"].get("compressed_aliases", False)
    require(type(compressed_mode) is bool, "Invalid compressed-alias mode")
    products = certificate["products"]
    flat = [(r, j, c, mon) for r, row in enumerate(norm["rows"])
            for j, (c, mon) in enumerate(row["terms"])]
    require(len(products) == len(flat), "Occurrence count mismatch")
    common = {}
    unit_ids = []
    all_categories = {"shared", "unit_shared", "private", "private_group", "flow", "equality_dummy", "unit_dummy"}
    for i, description in enumerate(final):
        require(description["kind"] in all_categories, "Unknown final-variable kind")
        if description["kind"] == "shared":
            v = description["normalized_variable"]
            require(type(v) is int and 0 <= v < len(norm["variables"]) and v not in common,
                    "Invalid shared representative")
            common[v] = i
        elif description["kind"] == "unit_shared":
            unit_ids.append(i)
    require(len(unit_ids) == 1, "Need exactly one shared unit")
    unit = unit_ids[0]
    private_ids, expected_groups, private_units = set(), defaultdict(set), set()
    private_occurrences, private_seconds = defaultdict(list), defaultdict(list)
    used_shared = set()
    for v, i in common.items():
        expected_groups[v].add(i)
    for product, (r, j, c, mon) in zip(products, flat):
        require(product["row"] == r and product["occurrence"] == j and product["sign"] == c,
                "Occurrence binding")
        a, b = product["logical_factors"]
        require(sorted(v for v in (a, b) if v is not None) == sorted(mon), "Logical-factor binding")
        require((len(mon) == 2) == (b is not None), "Homogenization provenance")
        require((len(mon) != 0) == (a is not None), "Private-factor provenance")
        p, s = product["factors"]
        require(type(p) is int and type(s) is int and 0 <= p < dimension and 0 <= s < dimension,
                "Product-coordinate range")
        if final[p]["kind"] == "private":
            require(p not in private_ids and final[p] == {"kind": "private", "normalized_variable": a,
                    "row": r, "occurrence": j}, "Private occurrence metadata")
        else:
            require(compressed_mode and final[p]["kind"] == "private_group" and
                    final[p]["normalized_variable"] == a, "Private group metadata")
        private_ids.add(p)
        private_occurrences[p].append([r, j])
        private_seconds[p].append(s)
        collapsed_square = square_mode and a is not None and a == b
        expected_factor = p if collapsed_square else (unit if b is None else common.get(b))
        require(s == expected_factor, "Shared-factor coordinate")
        if b is not None and not collapsed_square:
            used_shared.add(b)
        if a is None:
            private_units.add(p)
        else:
            expected_groups[a].add(p)
    require(private_ids == {i for i, d in enumerate(final) if d["kind"] in ("private", "private_group")},
            "Unused private coordinate")
    second_pair_owner = {}
    for p in private_ids:
        if final[p]["kind"] == "private_group":
            require(len(private_occurrences[p]) >= 2 and final[p]["occurrences"] == private_occurrences[p],
                    "Private group's full occurrence ledger")
        seconds = private_seconds[p]
        if p in seconds:
            require(seconds == [p], "Square-loop private alias was merged")
            continue
        require(len(seconds) == len(set(seconds)), "Duplicate factor edge in private group")
        for i, a in enumerate(seconds):
            for b in seconds[i+1:]:
                pair = tuple(sorted((a, b)))
                require(pair not in second_pair_owner, "Four-cycle in alias-factor graph")
                second_pair_owner[pair] = p
    require(used_shared == set(common), "Unused shared coordinate")
    require(set(expected_groups) == set(range(len(norm["variables"]))), "Missing logical alias class")

    cycles = certificate["equality_cycles"]
    require(len(cycles) == len(expected_groups), "Alias class count")
    cycle_variables, seen_groups = set(), set()
    for cycle in cycles:
        v, aliases = cycle["normalized_variable"], cycle["aliases"]
        require(v in expected_groups and v not in seen_groups, "Alias class binding")
        seen_groups.add(v)
        require(len(set(aliases)) == len(aliases) and not cycle_variables.intersection(aliases),
                "Repeated alias variable")
        base = expected_groups[v]
        dummies = set(aliases) - base
        require(base.issubset(aliases) and len(dummies) == (1 if len(base) == 2 else 0),
                "Alias class membership")
        require(all(final[i] == {"kind": "equality_dummy", "normalized_variable": v} for i in dummies),
                "Alias dummy binding")
        require(len(aliases) == 1 or len(aliases) >= 3, "Forbidden two-cycle")
        cycle_variables.update(aliases)
    units = certificate["unit_path"]
    require(len(units) >= 2 and len(set(units)) == len(units), "Unit path requires distinct endpoints")
    original_units = private_units | {unit}
    unit_dummies = set(units) - original_units
    require(original_units.issubset(units) and len(unit_dummies) == max(0, 2-len(original_units)),
            "Unit-path membership")
    require(all(final[i] == {"kind": "unit_dummy"} for i in unit_dummies), "Unit dummy metadata")
    require(not set(units).intersection(cycle_variables), "Unit aliases overlap ordinary classes")

    vertices, edges = certificate["vertices"], certificate["edges"]
    hubs, blocks = certificate["hub_vertices"], certificate["row_blocks"]
    require(bool(hubs) and len(set(hubs)) == len(hubs), "Invalid hub block")
    require(len(blocks) == len(norm["rows"]), "Row-block count")
    components = [hubs] + blocks
    vertex_owner = {}
    for component, block in enumerate(components):
        require(bool(block) and len(set(block)) == len(block), "Empty or duplicate block")
        for part, v in enumerate(block):
            require(type(v) is int and 0 <= v < len(vertices) and v not in vertex_owner,
                    "Vertex partition")
            vertex_owner[v] = component
            expected = {"kind": "hub", "index": part} if component == 0 else {
                "kind": "row", "row": component-1, "part": part}
            require(vertices[v] == expected, "Vertex metadata")
    require(set(vertex_owner) == set(range(len(vertices))), "Unassigned graph vertex")
    incident = [dict() for _ in vertices]
    adjacency = [[] for _ in vertices]
    seen_pairs, prescribed_ids, flow_ids = set(), set(), set()
    for eidx, edge in enumerate(edges):
        tail, head = edge["tail"], edge["head"]
        require(tail in vertex_owner and head in vertex_owner and tail != head, "Graph endpoint")
        pair = tuple(sorted((tail, head)))
        require(pair not in seen_pairs, "Parallel graph edges")
        seen_pairs.add(pair)
        c, mon = edge["coefficient"], edge["monomial"]
        if edge["kind"] == "prescribed":
            pidx = edge["product"]
            require(type(pidx) is int and 0 <= pidx < len(products) and pidx not in prescribed_ids,
                    "Repeated prescribed edge")
            prescribed_ids.add(pidx)
            product = products[pidx]
            require(c == product["sign"] and mon == product["factors"], "Prescribed edge value")
            require(vertex_owner[tail] == product["row"] + 1 and vertex_owner[head] == 0,
                    "Prescribed edge orientation/block")
        else:
            require(edge["kind"] == "free" and c == 1 and len(mon) == 1, "Invalid free edge")
            w = mon[0]
            require(type(w) is int and 0 <= w < dimension and w not in flow_ids,
                    "Repeated free-flow coordinate")
            flow_ids.add(w)
            owner = vertex_owner[tail]
            require(owner == vertex_owner[head], "Free edge crosses blocks")
            expected = {"kind": "flow", "component": "hub", "edge": eidx} if owner == 0 else {
                "kind": "flow", "component": "row", "row": owner-1, "edge": eidx}
            require(final[w] == expected, "Free-flow metadata")
            adjacency[tail].append(head)
            adjacency[head].append(tail)
        add(incident[tail], {tuple(sorted(mon)): c})
        add(incident[head], {tuple(sorted(mon)): -c})
    require(prescribed_ids == set(range(len(products))), "Missing prescribed edge")
    require(flow_ids == {i for i, d in enumerate(final) if d["kind"] == "flow"}, "Unused free flow")
    require(cycle_variables | set(units) | flow_ids == set(range(dimension)), "Final variable coverage")
    require(not flow_ids.intersection(cycle_variables | set(units)), "Flow/alias namespace overlap")
    for block in components:
        reached, todo = set(), [block[0]]
        while todo:
            v = todo.pop()
            if v in reached:
                continue
            reached.add(v)
            todo.extend(adjacency[v])
        require(reached == set(block), "Free block is disconnected")
        require(sum(len(adjacency[v]) for v in block) == 2*(len(block)-1), "Free block is not a tree")

    # Independent reconstruction from 2P as an actual sum of squares.
    twice = {}
    for divergence in incident:
        add(twice, multiply(divergence, divergence))
    for cycle in cycles:
        aliases = cycle["aliases"]
        if len(aliases) == 1:
            continue
        for a, b in zip(aliases, aliases[1:]+aliases[:1]):
            difference = {(a,): 1, (b,): -1}
            add(twice, multiply(difference, difference))
    differences = [{(units[0],): 1, (): -1}, {(units[-1],): 1, (): -1}]
    differences.extend({(a,): 1, (b,): -1} for a, b in zip(units, units[1:]))
    for difference in differences:
        add(twice, multiply(difference, difference))
    require(all(c % 2 == 0 for c in twice.values()), "Twice-energy has odd coefficient")
    expected_polynomial = {mon: c//2 for mon, c in twice.items()}
    terms = artifact["terms"]
    require(all(list(sorted(mon)) == mon for c, mon in terms), "Unsorted emitted monomial")
    require(len({tuple(mon) for c, mon in terms}) == len(terms), "Repeated emitted monomial")
    polynomial = sparse(terms, dimension)
    require(polynomial == expected_polynomial, "Full half-sum-of-squares polynomial mismatch")
    require(all(c in (-1, 1) for c in polynomial.values()), "Coefficient height exceeds one")
    require(polynomial.get(()) == 1, "Constant coefficient")
    require({i for mon in polynomial for i in mon} == set(range(dimension)), "Nonoccurring final variable")
    metrics = {
        "variables": dimension, "degree": max(map(len, polynomial)),
        "monomials": len(polynomial), "coefficient_height": max(map(abs, polynomial.values())),
        "individual_degree": max(max(Counter(mon).values()) for mon in polynomial if mon),
        "source_variables": len(source["variables"]), "source_rows": len(source["residuals"]),
        "normalized_variables": len(norm["variables"]), "normalized_rows": len(norm["rows"]),
        "occurrences": len(products), "shared_representatives": len(common),
        "unit_coordinates": len(units), "flow_variables": len(flow_ids),
        "equality_dummies": sum(d["kind"] == "equality_dummy" for d in final),
        "hubs": len(hubs), "graph_vertices": len(vertices), "graph_edges": len(edges),
        "maximum_graph_degree": max(len(d) for d in incident),
        "positive_coefficients": sum(c == 1 for c in polynomial.values()),
        "negative_coefficients": sum(c == -1 for c in polynomial.values()),
    }
    if "square_aliases" in artifact["metrics"]:
        metrics["square_aliases"] = square_mode
    if "compressed_aliases" in artifact["metrics"]:
        metrics["compressed_aliases"] = compressed_mode
    if "private_groups" in artifact["metrics"]:
        metrics["private_groups"] = len(private_ids)
    require(metrics["degree"] == 4 and metrics["individual_degree"] <= (4 if square_mode else 2),
            "Degree claim")
    require(metrics == artifact["metrics"], "Metric mismatch")
    require(len(flow_ids) == sum(len(block)-1 for block in components), "Flow-variable dimension")
    return metrics


def mutation_tests(source, artifact, certificate, digest):
    rejected = []
    def run(name, mutate):
        a, c = deepcopy(artifact), deepcopy(certificate)
        mutate(a, c)
        try:
            verify(source, a, c, digest)
        except (ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise ValueError("Corruption accepted: " + name)
    run("polynomial_sign", lambda a, c: a["terms"][0].__setitem__(0, -a["terms"][0][0]))
    run("source_digest", lambda a, c: c.__setitem__("source_sha256", "0"*64))
    run("missing_source_row", lambda a, c: c["normalization"]["rows"].pop())
    run("wrong_normalized_sign", lambda a, c: c["normalization"]["rows"][-1]["terms"][0].__setitem__(0,
        -c["normalization"]["rows"][-1]["terms"][0][0]))
    run("wrong_private_factor", lambda a, c: c["products"][0]["logical_factors"].__setitem__(0, None))
    run("missing_graph_edge", lambda a, c: c["edges"].pop())
    run("duplicate_unit_endpoint", lambda a, c: c["unit_path"].__setitem__(-1, c["unit_path"][0]))
    run("missing_alias", lambda a, c: c["equality_cycles"][0]["aliases"].pop())
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--artifact-dir", type=Path)
    parser.add_argument("--polynomial", type=Path)
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--mutations", action="store_true")
    args = parser.parse_args()
    raw = args.source.read_bytes()
    source = json.loads(raw)
    digest = hashlib.sha256(raw).hexdigest()
    require((args.artifact_dir is not None) != (args.polynomial is not None or args.certificate is not None),
            "Use either --artifact-dir or both --polynomial and --certificate")
    if args.artifact_dir is not None:
        polynomial_path = args.artifact_dir/"polynomial.json"
        certificate_path = args.artifact_dir/"certificate.json"
    else:
        require(args.polynomial is not None and args.certificate is not None, "Both explicit paths required")
        polynomial_path, certificate_path = args.polynomial, args.certificate
    artifact = json.loads(polynomial_path.read_text())
    certificate = json.loads(certificate_path.read_text())
    metrics = verify(source, artifact, certificate, digest)
    if args.artifact_dir is not None and (args.artifact_dir/"metrics.json").exists():
        require(json.loads((args.artifact_dir/"metrics.json").read_text()) == metrics, "Metrics file mismatch")
    rejected = mutation_tests(source, artifact, certificate, digest) if args.mutations else []
    receipt = {"status": "pass", "source_sha256": digest, "metrics": metrics,
               "checks": ["exact normalized source pullbacks", "topological monic constructors",
                          "complete alias-factor provenance", "simple graph and free spanning trees",
                          "unit path and equality-cycle namespace partition",
                          "complete half-sum-of-squares coefficient expansion", "all dimensions and degrees"],
               "mutations_rejected": rejected,
               "scope": "Finite algebraic artifact checks; unbounded proof and source consistency calibration remain separate."}
    output = json.dumps(receipt, sort_keys=True, indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
