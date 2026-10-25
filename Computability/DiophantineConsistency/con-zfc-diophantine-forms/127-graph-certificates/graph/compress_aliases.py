#!/usr/bin/env python3
"""Experimental C4-free alias compression of a verified graph artifact.

Reads a complete graph polynomial/certificate pair, merges only compatible
private aliases of the same logical variable, and reconstructs all coefficients.
Square-loop aliases remain separate. No consistency claim comes from this code.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import json
from pathlib import Path


def ensure(condition, message):
    if not condition:
        raise ValueError(message)


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, separators=(",", ":"))+"\n")


def compress(artifact, certificate):
    old_variables = artifact["variables"]
    products = certificate["products"]
    ensure(all(old_variables[p["factors"][0]]["kind"] == "private" for p in products),
           "Expected the uncompressed private-occurrence format")
    clusters, clusters_by_logical, pair_owner = [], defaultdict(list), {}
    private_cluster = {}
    for i, product in enumerate(products):
        private, second = product["factors"]
        logical = product["logical_factors"][0]
        ensure(private not in private_cluster, "Input private alias is reused")
        if private == second:
            cid = len(clusters)
            clusters.append({"logical": logical, "products": [i], "seconds": set(), "square": True})
            private_cluster[private] = cid
            continue
        choices = []
        for cid in clusters_by_logical[logical]:
            cluster = clusters[cid]
            if second in cluster["seconds"]:
                continue
            if any(tuple(sorted((second, s))) in pair_owner for s in cluster["seconds"]):
                continue
            choices.append(cid)
        if choices:
            cid = max(choices, key=lambda k: (len(clusters[k]["products"]), -k))
            cluster = clusters[cid]
            for s in cluster["seconds"]:
                pair_owner[tuple(sorted((second, s)))] = cid
            cluster["seconds"].add(second)
            cluster["products"].append(i)
        else:
            cid = len(clusters)
            clusters.append({"logical": logical, "products": [i], "seconds": {second}, "square": False})
            clusters_by_logical[logical].append(cid)
        private_cluster[private] = cid

    new_variables, renaming, cluster_new = [], {}, {}
    for old, description in enumerate(old_variables):
        if description["kind"] in ("equality_dummy", "unit_dummy"):
            continue
        if description["kind"] == "private":
            cid = private_cluster[old]
            if cid in cluster_new:
                renaming[old] = cluster_new[cid]
                continue
            cluster = clusters[cid]
            new = len(new_variables)
            cluster_new[cid] = new
            if len(cluster["products"]) == 1:
                metadata = deepcopy(description)
            else:
                occurrences = [[products[p]["row"], products[p]["occurrence"]]
                               for p in cluster["products"]]
                metadata = {"kind": "private_group", "normalized_variable": cluster["logical"],
                            "occurrences": occurrences}
        else:
            new = len(new_variables)
            metadata = deepcopy(description)
        new_variables.append(metadata)
        renaming[old] = new
    new_certificate = deepcopy(certificate)
    for product in new_certificate["products"]:
        product["factors"] = [renaming[v] for v in product["factors"]]
    for edge in new_certificate["edges"]:
        edge["monomial"] = [renaming[v] for v in edge["monomial"]]
    cycles = []
    for cycle in certificate["equality_cycles"]:
        logical = cycle["normalized_variable"]
        aliases = list(dict.fromkeys(renaming[v] for v in cycle["aliases"] if v in renaming))
        if len(aliases) == 2:
            aliases.append(len(new_variables))
            new_variables.append({"kind": "equality_dummy", "normalized_variable": logical})
        cycles.append({"normalized_variable": logical, "aliases": aliases})
    new_certificate["equality_cycles"] = cycles
    units = list(dict.fromkeys(renaming[v] for v in certificate["unit_path"] if v in renaming))
    while len(units) < 2:
        units.append(len(new_variables))
        new_variables.append({"kind": "unit_dummy"})
    new_certificate["unit_path"] = units

    # Reconstruct by the graph's edge-square and adjacent-edge formula.
    polynomial = {}
    def term(c, mon):
        key = tuple(sorted(mon))
        ensure(key not in polynomial and c in (-1, 1), "Coefficient collision after compression")
        polynomial[key] = c
    incident = [[] for _ in new_certificate["vertices"]]
    for edge in new_certificate["edges"]:
        c, mon = edge["coefficient"], edge["monomial"]
        term(1, mon+mon)
        incident[edge["tail"]].append((c, mon))
        incident[edge["head"]].append((-c, mon))
    for divergence in incident:
        for i, (c, left) in enumerate(divergence):
            for d, right in divergence[i+1:]:
                term(c*d, left+right)
    for cycle in cycles:
        aliases = cycle["aliases"]
        if len(aliases) == 1:
            continue
        for a in aliases:
            term(1, [a, a])
        for a, b in zip(aliases, aliases[1:]+aliases[:1]):
            term(-1, [a, b])
    term(1, [])
    for u in units:
        term(1, [u, u])
    for a, b in zip(units, units[1:]):
        term(-1, [a, b])
    term(-1, [units[0]])
    term(-1, [units[-1]])
    metrics = deepcopy(artifact["metrics"])
    metrics.update({"variables": len(new_variables), "monomials": len(polynomial),
        "equality_dummies": sum(v["kind"] == "equality_dummy" for v in new_variables),
        "positive_coefficients": sum(c == 1 for c in polynomial.values()),
        "negative_coefficients": sum(c == -1 for c in polynomial.values()),
        "private_groups": len(clusters), "compressed_aliases": True})
    result = {"schema": artifact["schema"], "domain": artifact["domain"],
        "variables": new_variables, "metrics": metrics,
        "terms": [[polynomial[mon], list(mon)] for mon in sorted(polynomial, key=lambda m: (len(m),m))]}
    summary = {"original_variables": len(old_variables), "variables": len(new_variables),
        "original_monomials": len(artifact["terms"]), "monomials": len(polynomial),
        "private_occurrences": len(products), "private_groups": len(clusters),
        "merges": len(products)-len(clusters), "protected_square_loops": sum(c["square"] for c in clusters),
        "group_sizes": dict(sorted(Counter(len(c["products"]) for c in clusters).items()))}
    return result, new_certificate, summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    polynomial, certificate, summary = compress(
        json.loads((args.input/"polynomial.json").read_text()),
        json.loads((args.input/"certificate.json").read_text()))
    write(args.output/"polynomial.json", polynomial)
    write(args.output/"certificate.json", certificate)
    write(args.output/"metrics.json", polynomial["metrics"])
    write(args.output/"COMPRESSION.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
