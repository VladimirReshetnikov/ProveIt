"""Independent topology and feature checks for compressed run certificates.

The source grammar is a separate required argument. The parser/compiler and
plain Candidate/Result record types are shared; graph composition, features,
and weighted span checking are reimplemented here. This is not a proof
assistant or an ambient 3-manifold embedding verifier.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from compressed_search import Candidate, Result, compile_grammar, source_digest, ResourceLimit


def normalize(xs):
    previous = []
    ans = []
    for x in xs:
        if x not in previous:
            previous.append(x)
        ans.append(previous.index(x))
    return tuple(ans)


def independent_feature(p: tuple[int, ...]) -> int:
    """Enumerate all subsets and test transversals, not a block product."""
    answer = 0
    for mask in range(1 << (len(p) - 1)):
        counts = [0] * (max(p) + 1)
        counts[p[0]] += 1
        for i in range(1, len(p)):
            if not ((mask >> (i - 1)) & 1):
                counts[p[i]] += 1
        if all(c == 1 for c in counts):
            answer |= 1 << mask
    return answer


def graph_components(n, edges):
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    labels = [-1] * n
    edgecounts, vertexcounts = [], []
    for start in range(n):
        if labels[start] != -1:
            continue
        label = len(edgecounts)
        stack = [start]
        labels[start] = label
        degsum = count = 0
        while stack:
            u = stack.pop()
            count += 1
            degsum += len(adjacency[u])
            for v in adjacency[u]:
                if labels[v] == -1:
                    labels[v] = label
                    stack.append(v)
        edgecounts.append(degsum // 2)
        vertexcounts.append(count)
    return labels, edgecounts, vertexcounts


def independent_compose(p, q, a, b, c):
    offset = max(p) + 1
    n = offset + max(q) + 1
    edges = [(p[a+i], offset+q[i]) for i in range(b)]
    labels, es, vs = graph_components(n, edges)
    if any(e != v - 1 for e, v in zip(es, vs)):
        return None
    outer = [labels[x] for x in p[:a]] + [labels[offset+x] for x in q[b:]]
    if len(set(outer)) != len(es):
        return None
    return normalize(outer)


def independent_disk_cap(p, q):
    offset = max(p) + 1
    labels, es, vs = graph_components(offset + max(q) + 1,
                                     [(x, offset+y) for x, y in zip(p, q)])
    return len(es) == 1 and es[0] == vs[0] - 1


def reconstructed_candidates(rule, tables, width):
    if rule.kind == "identity":
        return [Candidate(tuple(range(width)) * 2, 0, 0, ())]
    if rule.kind == "atoms":
        return [Candidate(p, c, q, (i,)) for i, (p, c, q) in enumerate(rule.args)]
    if rule.kind == "union":
        return [Candidate(x.partition, x.cost, x.charge, (child, i))
                for child in rule.args for i, x in enumerate(tables[child])]
    a, b = rule.args
    out = []
    for i, x in enumerate(tables[a]):
        for j, y in enumerate(tables[b]):
            p = independent_compose(x.partition, y.partition, width, width, width)
            if p is not None:
                out.append(Candidate(p, x.cost+y.cost, x.charge ^ y.charge, (a, i, b, j)))
    return out


def check_reduction(candidates, selection, width, charges):
    if not isinstance(selection, list) or any(type(i) is not int for i in selection):
        raise ValueError("selection must be a list of original integer indices")
    if len(set(selection)) != len(selection) or any(i < 0 or i >= len(candidates) for i in selection):
        raise ValueError("duplicated or out-of-range original index")
    dimension = 1 << (2 * width - 1)
    for sector in {candidates[i].charge for i in selection}:
        if sum(candidates[i].charge == sector for i in selection) > dimension:
            raise ValueError("representative dimension bound exceeded")
    selected = sorted(selection, key=lambda i: candidates[i].cost)
    pivots = {}
    position = 0
    for item in sorted(candidates, key=lambda c: c.cost):
        while position < len(selected) and candidates[selected[position]].cost <= item.cost:
            x = candidates[selected[position]]
            row = independent_feature(x.partition)
            while row:
                key = x.charge, row.bit_length() - 1
                if key in pivots:
                    row ^= pivots[key]
                else:
                    pivots[key] = row
                    break
            position += 1
        row = independent_feature(item.partition)
        while row:
            key = item.charge, row.bit_length() - 1
            if key not in pivots:
                raise ValueError("a source row lacks a no-more-expensive same-charge expansion")
            row ^= pivots[key]


def check(source: dict, certificate: dict, *, max_feature_dimension=65536,
          max_pairs=10000000) -> Result:
    if certificate.get("format") != "binary-patch-run-v1":
        raise ValueError("unknown certificate format")
    if certificate.get("source_digest") != source_digest(source):
        raise ValueError("certificate is not bound to this independently supplied grammar")
    program = compile_grammar(source)
    if max_feature_dimension < 1 or (2*program.width-1) >= max_feature_dimension.bit_length():
        raise ResourceLimit("checker feature budget exhausted")
    selections = certificate.get("selections")
    if not isinstance(selections, list) or len(selections) != len(program.rules):
        raise ValueError("certificate omits or adds a compiled table")
    if certificate.get("root") != program.root:
        raise ValueError("incorrect output rule")
    tables = []
    pairs = 0
    for rule, selection in zip(program.rules, selections):
        if rule.kind == "concat":
            a, b = rule.args
            pairs += len(tables[a]) * len(tables[b])
            if pairs > max_pairs:
                raise ResourceLimit("checker composition budget exhausted")
        generated = reconstructed_candidates(rule, tables, program.width)
        check_reduction(generated, selection, program.width, program.charges)
        tables.append([generated[i] for i in selection])
    return Result(program, tables, selections, source_digest(source), {"checked_pairs": pairs})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("grammar", type=Path)
    ap.add_argument("certificate", type=Path)
    args = ap.parse_args()
    source = json.loads(args.grammar.read_text())
    try:
        result = check(source, json.loads(args.certificate.read_text()))
        print(json.dumps({"status": "VALID_ABSTRACT_RUN", "metrics": result.metrics}, indent=2))
    except ResourceLimit as exc:
        print(json.dumps({"status": "UNKNOWN_RESOURCE_LIMIT", "reason": str(exc)}))
    except (ValueError, KeyError, IndexError, TypeError) as exc:
        print(json.dumps({"status": "INVALID_CERTIFICATE", "reason": str(exc)}))
        raise SystemExit(1)


if __name__ == "__main__":
    main()
