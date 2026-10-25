#!/usr/bin/env python3
"""A height-one quartic compiler using a simple graph and shared factors.

New graph/alias compiler, 2026-10-24. The normalization is adapted from the
credited incoming Height One and Degree 464 compiler. Standard library only.
All variables are unrestricted integers; there are no polynomial parameters.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")


def normalize(source):
    n = len(source["variables"])
    variables = [{"kind": "original", "source_index": i} for i in range(n)]
    coefficients = set()

    def need(c):
        if c > 1 and c not in coefficients:
            coefficients.add(c)
            need(c // 2)

    for row in source["residuals"]:
        for c, mon in row["terms"]:
            if type(c) is not int or not c or len(mon) > 2:
                raise ValueError("Nonzero integral quadratic rows required")
            if any(type(i) is not int or i < 0 or i >= n for i in mon):
                raise ValueError("Bad source variable")
            need(abs(c))
    constants, rows = {}, []
    for c in sorted(coefficients):
        idx = len(variables)
        constants[c] = idx
        variables.append({"kind": "constant", "value": c})
        half = [] if c // 2 == 1 else [constants[c // 2]]
        terms = [[1, [idx]], [-1, half], [-1, half]]
        if c % 2:
            terms.append([-1, []])
        rows.append({"kind": "constant", "value": c, "terms": terms})
    scales = {}
    for c, v in sorted({(abs(c), mon[0]) for row in source["residuals"]
                        for c, mon in row["terms"] if abs(c) > 1 and len(mon) == 2}):
        idx = len(variables)
        scales[c, v] = idx
        variables.append({"kind": "scale", "coefficient": c, "variable": v})
        rows.append({"kind": "scale", "coefficient": c, "variable": v,
                     "terms": [[1, [idx]], [-1, [constants[c], v]]]})
    for r, row in enumerate(source["residuals"]):
        terms = []
        for c, mon in row["terms"]:
            a = abs(c)
            if a == 1:
                out = list(mon)
            elif not mon:
                out = [constants[a]]
            elif len(mon) == 1:
                out = [constants[a], mon[0]]
            else:
                out = [scales[a, mon[0]], mon[1]]
            terms.append([1 if c > 0 else -1, out])
        if not terms:
            raise ValueError("Remove empty source rows before compilation")
        rows.append({"kind": "source", "source_row": r, "terms": terms})
    return {"variables": variables, "rows": rows, "original_variables": n,
            "constant_count": len(constants), "scale_count": len(scales)}


def orient(norm, square_aliases=False):
    """Deterministic local optimization; no assertion of global optimality."""
    flat = [(r, j, sign, mon) for r, row in enumerate(norm["rows"])
            for j, (sign, mon) in enumerate(row["terms"])]
    frequency = Counter(v for _, _, _, mon in flat if len(mon) == 2 for v in mon)
    pairs = []
    for r, j, sign, mon in flat:
        if len(mon) == 2:
            a, b = mon
            # First coordinate is private; second is shared.
            if (frequency[a], -a) > (frequency[b], -b):
                a, b = b, a
        else:
            a = mon[0] if mon else None
            b = None
        pairs.append([a, b])

    def score(ps):
        private = Counter(a for a, b in ps if a is not None)
        shared = {b for a, b in ps if b is not None and not (square_aliases and a == b)}
        dummy = sum(private[v] + (v in shared) == 2 for v in range(len(norm["variables"])))
        return len(shared) + dummy

    # A group move can remove a common representative even when single flips cannot.
    current = score(pairs)
    for sweep in range(12):
        changed = False
        for v in sorted({b for a, b in pairs if b is not None}):
            positions = [i for i, (a, b) in enumerate(pairs) if b == v]
            if not positions or any(pairs[i][0] == v for i in positions):
                continue
            candidate = [p[:] for p in pairs]
            for i in positions:
                candidate[i].reverse()
            value = score(candidate)
            if value < current:
                pairs, current, changed = candidate, value, True
        for i, (a, b) in enumerate(pairs):
            if a is None or b is None or a == b:
                continue
            pairs[i] = [b, a]
            value = score(pairs)
            if value < current:
                current, changed = value, True
            else:
                pairs[i] = [a, b]
        if not changed:
            break
    return flat, pairs


def compile_graph(source, hubs, square_aliases=False):
    if type(hubs) is not int or hubs < 1:
        raise ValueError("A positive number of hubs is required")
    norm = normalize(source)
    flat, orientations = orient(norm, square_aliases)
    variables, groups, units, products = [], defaultdict(list), [], []

    def fresh(kind, **metadata):
        idx = len(variables)
        variables.append({"kind": kind, **metadata})
        return idx

    common = {}
    for v in sorted({b for a, b in orientations if b is not None and not (square_aliases and a == b)}):
        c = fresh("shared", normalized_variable=v)
        common[v] = c
        groups[v].append(c)
    unit = fresh("unit_shared")
    units.append(unit)
    for i, ((r, j, sign, mon), (a, b)) in enumerate(zip(flat, orientations)):
        private = fresh("private", normalized_variable=a, row=r, occurrence=j)
        if a is None:
            units.append(private)
        else:
            groups[a].append(private)
        other = private if square_aliases and a == b and a is not None else (unit if b is None else common[b])
        products.append({"row": r, "occurrence": j, "sign": sign,
                         "factors": [private, other], "logical_factors": [a, b]})

    # The free edges form one path in each row block and one common hub path.
    vertices = [{"kind": "hub", "index": i} for i in range(hubs)]
    edges, blocks = [], []
    next_product = 0
    for r, row in enumerate(norm["rows"]):
        s = len(row["terms"])
        count = (s + hubs - 1) // hubs
        block = list(range(len(vertices), len(vertices) + count))
        vertices.extend({"kind": "row", "row": r, "part": i} for i in range(count))
        for j in range(s):
            p = products[next_product + j]
            edges.append({"kind": "prescribed", "tail": block[j // hubs],
                          "head": (next_product + j) % hubs,
                          "coefficient": p["sign"], "monomial": p["factors"],
                          "product": next_product + j})
        for left, right in zip(block, block[1:]):
            w = fresh("flow", component="row", row=r, edge=len(edges))
            edges.append({"kind": "free", "tail": left, "head": right,
                          "coefficient": 1, "monomial": [w]})
        blocks.append(block)
        next_product += s
    for left in range(hubs - 1):
        w = fresh("flow", component="hub", edge=len(edges))
        edges.append({"kind": "free", "tail": left, "head": left + 1,
                      "coefficient": 1, "monomial": [w]})

    pol = {}

    def term(c, mon):
        key = tuple(sorted(mon))
        if c not in (-1, 1) or key in pol:
            raise ValueError(f"Coefficient collision at {key}")
        pol[key] = c

    incident = [[] for _ in vertices]
    graph_pairs = set()
    for i, e in enumerate(edges):
        pair = tuple(sorted((e["tail"], e["head"])))
        if pair[0] == pair[1] or pair in graph_pairs:
            raise ValueError("The incidence graph must be simple")
        graph_pairs.add(pair)
        c, m = e["coefficient"], e["monomial"]
        term(1, m + m)
        incident[e["tail"]].append((c, m))
        incident[e["head"]].append((-c, m))
    for row in incident:
        for i, (c, m) in enumerate(row):
            for d, n in row[i + 1:]:
                term(c * d, m + n)

    cycles = []
    for v, aliases in sorted(groups.items()):
        if len(aliases) == 2:
            aliases.append(fresh("equality_dummy", normalized_variable=v))
        if len(aliases) > 1:
            for a in aliases:
                term(1, [a, a])
            for a, b in zip(aliases, aliases[1:] + aliases[:1]):
                term(-1, [a, b])
        cycles.append({"normalized_variable": v, "aliases": aliases})
    while len(units) < 2:
        units.append(fresh("unit_dummy"))
    term(1, [])
    for a in units:
        term(1, [a, a])
    for a, b in zip(units, units[1:]):
        term(-1, [a, b])
    term(-1, [units[0]])
    term(-1, [units[-1]])
    terms = [[pol[m], list(m)] for m in sorted(pol, key=lambda m: (len(m), m))]
    used = set(i for m in pol for i in m)
    if used != set(range(len(variables))):
        raise ValueError("Unused final variable")
    metrics = {"variables": len(variables), "degree": max(map(len, pol)),
               "monomials": len(terms), "coefficient_height": 1,
               "individual_degree": max(Counter(m).most_common(1)[0][1] for m in pol if m),
               "source_variables": len(source["variables"]), "source_rows": len(source["residuals"]),
               "normalized_variables": len(norm["variables"]), "normalized_rows": len(norm["rows"]),
               "occurrences": len(flat), "shared_representatives": len(common),
               "unit_coordinates": len(units), "flow_variables": sum(v["kind"] == "flow" for v in variables),
               "equality_dummies": sum(v["kind"] == "equality_dummy" for v in variables),
               "hubs": hubs, "square_aliases": square_aliases,
               "graph_vertices": len(vertices), "graph_edges": len(edges),
               "maximum_graph_degree": max(map(len, incident)),
               "positive_coefficients": sum(c == 1 for c, m in terms),
               "negative_coefficients": sum(c == -1 for c, m in terms)}
    artifact = {"schema": "graph-height-one-quartic-v1", "domain": "unrestricted integers",
                "variables": variables, "terms": terms, "metrics": metrics}
    certificate = {"schema": "graph-height-one-certificate-v1", "normalization": norm,
                   "products": products, "vertices": vertices, "edges": edges,
                   "row_blocks": blocks, "hub_vertices": list(range(hubs)),
                   "equality_cycles": cycles, "unit_path": units}
    return artifact, certificate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--hubs", type=int, default=128)
    parser.add_argument("--square-aliases", action="store_true")
    args = parser.parse_args()
    raw = args.source.read_bytes()
    artifact, certificate = compile_graph(json.loads(raw), args.hubs, args.square_aliases)
    certificate["source_sha256"] = hashlib.sha256(raw).hexdigest()
    dump(args.out / "polynomial.json", artifact)
    dump(args.out / "certificate.json", certificate)
    dump(args.out / "metrics.json", artifact["metrics"])
    print(json.dumps(artifact["metrics"], sort_keys=True))


if __name__ == "__main__":
    main()
