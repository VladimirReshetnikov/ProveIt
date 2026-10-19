#!/usr/bin/env python3
"""Audit an abstract routed grammar; this does not certify a binary machine.

The input constraint format and property recurrence are inherited from the
ProveIt routed245 package. This independent implementation uses only the
Python standard library. See NOTICE.txt for attribution.
"""
import argparse
import json
from functools import lru_cache
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions must be enabled; do not use Python -O.")

p = argparse.ArgumentParser()
p.add_argument("grammar", type=Path)
p.add_argument("--route-grammar", type=Path, required=True)
p.add_argument("--constraints", type=Path, required=True)
p.add_argument("--bootstrap", type=Path, required=True)
p.add_argument("--source-seed", type=Path)
p.add_argument("--semantic-rows", type=Path)
p.add_argument("--parts", type=Path)
p.add_argument("--output", type=Path)
a = p.parse_args()

d = json.loads(a.grammar.read_text())
g = {w: (l, r) for w, l, r in d["rules"]}
assert len(g) == len(d["rules"]) == d["rules_count"]
lines = a.route_grammar.read_text().splitlines()
n, nr, na = map(int, lines[0].split())
old = {}
for row in lines[1:n + 1]:
    k, w, q = row.split()
    old[w] = (w[:int(k)], w[int(k):])
roots = set(lines[n + 1:n + 1 + nr])
allowed = {c: int(mask) for c, mask in
           map(str.split, lines[n + 1 + nr:])}
assert len(allowed) == na
for w, (l, r) in g.items():
    assert w == l + r and l and r
    for bit, child in enumerate((l, r)):
        assert child in g or child in allowed
        if child in allowed:
            assert allowed[child] & (1 << bit)

def project(w, bits):
    for bit in bits:
        assert bit in "01"
        w = g[w][int(bit)]
    return w

routes = {(r["source"], r["read"]): r["word"] for r in d["routes"]}
assert len(routes) == len(d["routes"])
tokens = iter(a.constraints.read_text().split())
ng = int(next(tokens))
groups = []
route_checks = 0
for _ in range(ng):
    s, b, w, nc = [next(tokens) for _ in range(4)]
    key = (int(s), int(b))
    groups.append(key)
    for _ in range(int(nc)):
        pre, target = next(tokens), next(tokens)
        assert project(routes[key], pre) == target
        route_checks += 1
assert set(routes) == set(groups)
ne, original, natoms = [int(next(tokens)) for _ in range(3)]
expr = []
for _ in range(ne):
    kind = next(tokens)
    if kind == "L":
        expr.append((kind,))
    elif kind == "W":
        expr.append((kind, next(tokens)))
    else:
        assert kind == "N"
        expr.append((kind, int(next(tokens)), int(next(tokens))))
atoms = {next(tokens): int(next(tokens)) for _ in range(natoms)}
assert list(tokens) == [] and set(atoms) == set(allowed)

boot = a.bootstrap.read_text().splitlines()
assert int(boot[0]) == len(boot) - 1
for line in boot[1:]:
    w, pre, target = line.split()
    roots.add(w)
    assert project(w, pre) == target
assert roots == set(d["roots"])
seen = set()
stack = list(roots | set(routes.values()))
while stack:
    w = stack.pop()
    if len(w) == 1 or w in seen:
        continue
    seen.add(w)
    stack.extend(g[w])
assert seen == set(g)

def join(l, r):
    return (l[0] + 1, max(l[0] + 1, l[1], r[1]),
            max(l[2], r[2]) + 1)

@lru_cache(None)
def ep(i):
    row = expr[i]
    if row[0] == "L":
        return (0, 0, 0)
    if row[0] == "W":
        return wp(row[1])
    return join(ep(row[1]), ep(row[2]))

@lru_cache(None)
def wp(w):
    if len(w) == 1:
        return ep(atoms[w])
    return join(*(wp(x) for x in g.get(w, old.get(w))))

props = ep(original)
assert props[1] <= 7 and props[2] <= 64
if "properties" in d:
    assert list(props) == d["properties"]
source_check = None
if a.source_seed:
    seed = json.loads(a.source_seed.read_text())
    assert set(seed["roots"]) == roots
    assert seed["modified_AX_word"] in roots
    if "source_variant" in seed:
        assert a.semantic_rows
        ex = json.loads(a.semantic_rows.read_text())["fine_atom_expansions"]
        expand = lambda w: [q for c in w for q in ex[c]]
        spec = seed["source_variant"]
        order = seed.get("axiom_push_order", list(range(8, 0, -1)))
        if "raw_AX_rows" in spec:
            raw = spec["raw_AX_prefix"] + "".join(
                spec["raw_AX_rows"][8-q] for q in order) + spec["raw_AX_tail"]
        else:
            assert order == list(range(8, 0, -1))
            raw = spec["raw_AX_word"]
        assert expand(raw) == expand(seed["modified_AX_word"])
        source_check = "PASS_FINE_ATOM_EXPANSION_OF_DECLARED_VARIANT"
    elif "axiom_push_order" in seed:
        assert a.parts
        parts = json.loads(a.parts.read_text())
        raw = parts["prefix"] + "".join(
            parts["rows"][8-q] for q in seed["axiom_push_order"]) + parts["tail"]
        assert raw == seed["modified_AX_word"]
        source_check = "PASS_DECLARED_WHOLE_ROW_PERMUTATION"

out = dict(status="PASS_ABSTRACT_GRAMMAR_ONLY", rules=len(g),
           routed_projection_checks=route_checks,
           bootstrap_projection_checks=len(boot)-1,
           source_properties=dict(lead=props[0], maximum_zero_run=props[1],
                                  maximum_leaf_depth=props[2]),
           all_rules_reachable=True, declared_source_expansion=source_check,
           scanner245_eligible=(props[1] <= 6),
           scope="Finite words, projections, orientation and source AST properties; no binary TM or consistency-equivalence certificate")
print(json.dumps(out, indent=2))
if a.output:
    a.output.write_text(json.dumps(out, indent=2) + "\n")
