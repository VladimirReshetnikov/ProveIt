#!/usr/bin/env python3
"""Proof-producing CD screen for rho8 restrictions other than its U slot."""
import argparse
import heapq
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'theory_notes'))
from restricted_lukasiewicz import C, canonical, detach, polish, size, subsumes


def search(slot, replacement, extra, seconds, maxsize, maxprocessed):
    terms = dict(a=0, b=1, c=2, u=3)
    replacement_term = terms.get(replacement, replacement)
    if len(replacement) == 2 and all(x in terms for x in replacement):
        replacement_term = C(terms[replacement[0]], terms[replacement[1]])
    terms[slot] = replacement_term
    a, b, c, u = (terms[k] for k in ('a', 'b', 'c', 'u'))
    axioms = [canonical(C(C(C(c, u), a), C(C(a, c), C(b, c))))]
    if extra in ('truth', 'both', 'truth_identity', 'truth_dne'):
        axioms.append('t')
    if extra in ('explosion', 'both'):
        axioms.append(C('f', 0))
    if extra in ('identity', 'truth_identity'):
        axioms.append(C(0, 0))
    if extra in ('dne', 'truth_dne'):
        axioms.append(C(C(C(0, 'f'), 'f'), 0))
    if replacement == 'reduced':
        a, c, u = 0, 1, 2
        axioms[0] = canonical(C(C(C(c, u), a), C(C(a, c), c)))
    targets = {
        'I': C(0, 0), 'K': C(0, C(1, 0)),
        'B': C(C(0, 1), C(C(1, 2), C(0, 2))),
        'S': C(C(0, C(1, 2)), C(C(0, 1), C(0, 2))),
        'Peirce': C(C(C(0, 1), 0), 0),
    }
    nodes, processed, pending, known, found = [], [], [], {}, {}
    started = time.monotonic()

    def add(term, proof):
        if term is None or size(term) > maxsize or term in known:
            return
        if any(size(old) <= size(term) and subsumes(old, term) for old in known):
            return
        number = len(nodes)
        known[term] = number
        nodes.append((term, proof))
        heapq.heappush(pending, (size(term), number))
        for name, target in targets.items():
            if name not in found and subsumes(term, target):
                found[name] = number
                print('FOUND', name, number, polish(term), flush=True)

    for ax in axioms:
        add(ax, 'axiom')
    while pending and len(processed) < maxprocessed and time.monotonic() - started < seconds:
        _, i = heapq.heappop(pending)
        major = nodes[i][0]
        for j in processed + [i]:
            minor = nodes[j][0]
            add(detach(major, minor), [i, j])
            if i != j:
                add(detach(minor, major), [j, i])
        processed.append(i)
        if {'K', 'B', 'Peirce'} <= found.keys() or {'K', 'S', 'Peirce'} <= found.keys():
            break
    for term, proof in nodes:
        if proof != 'axiom':
            assert detach(nodes[proof[0]][0], nodes[proof[1]][0]) == term
    result = {
        'slot': slot, 'replacement': replacement, 'extra': extra,
        'maxsize': maxsize, 'maxprocessed': maxprocessed,
        'seconds': time.monotonic() - started, 'processed': len(processed),
        'node_count': len(nodes), 'saturated_within_size_bound': not pending,
        'found': found,
        'derivations': [dict(formula=polish(t), term=t, proof=p) for t, p in nodes],
    }
    destination = Path(__file__).parent / f'restricted_{slot}_{replacement}_{extra}.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'derivations'}), flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--slot', choices=['a', 'b', 'c', 'u'], default='b')
    ap.add_argument('--replacement', default='t')
    ap.add_argument('--extra', choices=['none', 'truth', 'explosion', 'both', 'identity', 'truth_identity', 'dne', 'truth_dne'], default='truth')
    ap.add_argument('--seconds', type=float, default=90)
    ap.add_argument('--maxsize', type=int, default=41)
    ap.add_argument('--maxprocessed', type=int, default=2000)
    args = ap.parse_args()
    search(args.slot, args.replacement, args.extra, args.seconds, args.maxsize, args.maxprocessed)
