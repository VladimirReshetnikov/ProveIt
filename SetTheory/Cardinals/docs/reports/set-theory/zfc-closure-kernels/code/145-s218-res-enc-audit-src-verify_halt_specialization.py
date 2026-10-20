#!/usr/bin/env python3
"""Fresh compact invariant and exact CFG transport for a specialized halt test.

The unbounded local macro argument is the three-case proof in halt_specialization.md.
This program verifies its exact syntax, inductive input premise, and all context
edges. It does not use a finite bound on the concrete register values.
"""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json
from environment import BASE_SOURCE, s

SEED = (3, 0, 0, 0, 3, 0, 0, 0, 0)
PATH = '1110100101'
LO, HI = 4598, 4610


def need(x, why):
    if not x:
        raise ValueError(why)


def invariant(rows, graph):
    facts = [None] * len(rows)
    start = tuple(1 if x == 0 else 2 for x in SEED)
    facts[0] = start
    todo = deque([0])

    def posts(i, values):
        op, a = rows[i][1:]
        destinations = graph[i][1]
        if op == 'CH': return []
        if op == 'CI':
            new = list(values); new[a] = 2
            return [(destinations[0], tuple(new))]
        if op == 'CD':
            result = []
            if values[a] & 1:
                new = list(values); new[a] = 1
                result.append((destinations[0], tuple(new)))
            if values[a] & 2:
                new = list(values); new[a] = 3
                result.append((destinations[1], tuple(new)))
            return result
        return [(destinations[0], values)]

    work = 0
    while todo:
        i = todo.popleft(); work += 1
        for j, post in posts(i, facts[i]):
            joined = post if facts[j] is None else tuple(a | b for a, b in zip(post, facts[j]))
            if joined != facts[j]:
                facts[j] = joined; todo.append(j)
    need(all((a | b) == b for a, b in zip(start, facts[0])), 'Certificate omits the seed')
    edges = 0
    for i, values in enumerate(facts):
        if values is None: continue
        for j, post in posts(i, values):
            need(facts[j] is not None and all((a | b) == b for a, b in zip(post, facts[j])),
                 'Certificate is not inductive')
            edges += 1
    return facts, work, edges


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--variant', choices=['reuse_e', 'six_leaf', 'six_leaf2'], default='reuse_e')
    ap.add_argument('--candidate', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args(); args.out.mkdir(parents=True, exist_ok=True)
    raw = BASE_SOURCE.read_bytes(); old = json.loads(raw); tree = s.tree(old)
    oldgraph = s.graph_intervals(old)
    need(s.graph_arithmetic(old)[0] == oldgraph, 'Old CFG resolvers disagree')
    facts, work, certificate_edges = invariant(old, oldgraph)
    need(facts[LO][6] == 1, 'R6 is not proved zero at the unique macro entry')
    incoming = [(i, j) for i, (_, targets) in enumerate(oldgraph)
                for j in targets if not LO <= i < HI and LO <= j < HI]
    outgoing = [(i, j) for i in range(LO, HI) for j in oldgraph[i][1] if not LO <= j < HI]
    need(incoming == [(39, LO)] and outgoing == [(4608, HI)], 'Unexpected macro boundary edge')
    part = tree
    for bit in PATH: part = part[int(bit)]
    d5, d6 = ('CD', 5), ('CD', 6)
    c1, c2, b1, halt = ('CC', 1), ('CC', 2), ('CB', 1), ('CH', None)
    u = ((d6, c2), b1)
    equality = (((d5, u), d6), ((d5, c1), u))
    need(part[0] == ('CI', 6) and part[1][0] == (equality, halt),
         'Old region is not exactly CI6 followed by the pinned equality-and-halt macro')
    macros = {
        'reuse_e': (d5, (equality, halt)),
        'six_leaf': ((d5, ((d5, b1), halt)), (d5, c1)),
        'six_leaf2': (d5, ((d5, ((d5, c1), b1)), halt)),
    }
    macro = macros[args.variant]
    need(s.boundary(macro) == (0, 0, True), 'Replacement macro has escaping control')
    candidate_tree = s.replace(tree, PATH, (macro, part[1][1]))
    new = s.sites(candidate_tree)
    if args.candidate:
        need(json.loads(args.candidate.read_text()) == new, 'Candidate differs from the exact proved replacement')
    newgraph = s.graph_intervals(new)
    need(s.graph_arithmetic(new)[0] == newgraph, 'New CFG resolvers disagree')
    newhi = LO + len(s.sites(macro))
    shift = newhi - HI
    need([x[1:] for x in old[:LO] + old[HI:]] == [x[1:] for x in new[:LO] + new[newhi:]],
         'Replacement changes the outside primitive word')

    def remap(i):
        if i < LO: return i
        if i >= HI: return i + shift
        need(i == LO, 'An outside edge enters the middle of the macro')
        return LO

    matched = 0
    for i, (effect, successors) in enumerate(oldgraph):
        if LO <= i < HI: continue
        need(newgraph[remap(i)] == [effect, [remap(j) for j in successors]],
             'Outside source effect or guarded edge changed')
        matched += len(successors)
    new_incoming = [(i, j) for i, (_, targets) in enumerate(newgraph)
                    for j in targets if not LO <= i < newhi and LO <= j < newhi]
    need(new_incoming == [(39, LO)], 'Replacement introduces an unexpected external entry')
    normal_exits = [(i, j) for i in range(LO, newhi) for j in newgraph[i][1] if not LO <= j < newhi]
    need(normal_exits and all(j == newhi for i, j in normal_exits), 'Replacement normal exit differs')
    # A second, fresh abstract proof on the candidate is useful independently
    # of the context-equivalence argument; it has the same small domain.
    newfacts, newwork, new_certificate_edges = invariant(new, newgraph)
    need(newfacts[LO][6] == 1, 'Candidate does not independently prove the input premise')
    outbytes = s.compact(new)
    (args.out / 'sites.json').write_bytes(outbytes)
    factsbytes = (json.dumps(facts, separators=(',', ':')) + '\n').encode()
    (args.out / 'zero_facts.json').write_bytes(factsbytes)
    (args.out / 'candidate_zero_facts.json').write_text(json.dumps(newfacts, separators=(',', ':')) + '\n')
    result = {
        'status': 'INDUCTIVE_ZERO_AND_EXACT_HALT_SPECIALIZATION_CONTEXT_PASS',
        'variant': args.variant, 'source_prefix': PATH,
        'old_interval': [LO, HI], 'new_interval': [LO, newhi],
        'external_incoming': incoming, 'normal_outgoing_old': outgoing,
        'normal_outgoing_new': normal_exits,
        'old_abstract_entry': facts[LO], 'new_abstract_entry': newfacts[LO],
        'bit_meanings': {'1': 'zero', '2': 'positive', '3': 'either'},
        'old_fixed_point_work_items': work, 'new_fixed_point_work_items': newwork,
        'old_inductive_edges_rechecked': certificate_edges,
        'new_inductive_edges_rechecked': new_certificate_edges,
        'outside_guarded_edges_matched': matched,
        'source_metrics': s.metrics(candidate_tree),
        'old_source_sha256': hashlib.sha256(raw).hexdigest(),
        'new_source_sha256': hashlib.sha256(outbytes).hexdigest(),
        'zero_facts_sha256': hashlib.sha256(factsbytes).hexdigest(),
        'macro_contract': 'Under R6=0, halt iff entry R5=1; otherwise return normally with R5=R6=0 and every other register unchanged.',
        'unbounded_macro_proof': 'Three cases R5=0, R5=1, R5>=2; the remaining clear loop decreases R5 until zero. See halt_specialization.md.',
        'scope': 'Executable ordinary finite induction and exact source context transport. This is not a proof-assistant kernel certificate or a compilation claim.'
    }
    (args.out / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
