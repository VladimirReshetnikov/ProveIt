#!/usr/bin/env python3
"""Audit literal decoder sharing and limited increment-order perturbations.

The cost is the number of distinct ordered internal subtrees, NOT the number
of states in a synthesized binary machine. This deliberately does not claim
that changing adjacent leaves is legal when control can enter their interior.
It is a reproducible local cost landscape for later certified optimization.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

if sys.flags.optimize:
    raise RuntimeError('Audit scripts require assertions; run without python -O.')


def audit(path):
    raw = Path(path).read_bytes()
    body = raw.decode().split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', body)
    assert len(nodes) == 6459
    leaves = []
    def walk(i, path=''):
        for side, edge in enumerate(nodes[i]):
            if edge.startswith('CN '):
                walk(int(edge[3:]), path + str(side))
            else:
                leaves.append((i, side, edge, path + str(side)))
    walk(0)
    pairs = [(a,b) for a,b in zip(leaves, leaves[1:]) if a[2].startswith('CI ') and b[2].startswith('CI ') and a[2] != b[2]]
    def cost(changed_pairs=()):
        changed = {}
        for j in changed_pairs:
            a,b = pairs[j]
            assert (a[0],a[1]) not in changed and (b[0],b[1]) not in changed
            changed[a[0],a[1]] = b[2]
            changed[b[0],b[1]] = a[2]
        interned = {}
        def visit(i):
            signature = []
            for side, edge in enumerate(nodes[i]):
                edge = changed.get((i,side), edge)
                signature.append(visit(int(edge[3:])) if edge.startswith('CN ') else edge)
            key = tuple(signature)
            if key not in interned:
                interned[key] = 'N' + str(len(interned))
            return interned[key]
        visit(0)
        return len(interned)
    classes = sorted({(a[2],b[2]) for a,b in pairs})
    masks = []
    for mask in range(2**len(classes)):
        selected = [j for j,(a,b) in enumerate(pairs) if mask & (1 << classes.index((a[2],b[2])))]
        masks.append({'mask': mask, 'swapped_pairs': len(selected), 'distinct_internal_subtrees': cost(selected)})
    depths = Counter(len(x[3]) for x in leaves)
    return {
        'program_sha256': hashlib.sha256(raw).hexdigest(),
        'tree_internal_nodes': len(nodes), 'tree_leaves': len(leaves),
        'syntactic_hashcons_internal_nodes': cost(),
        'syntactic_hashcons_leaf_labels': len({x[2] for x in leaves}),
        'maximum_depth': max(depths), 'minimum_depth': min(depths),
        'leaf_depth_histogram': dict(sorted(depths.items())),
        'leaf_operations': dict(sorted(Counter(x[2] for x in leaves).items())),
        'adjacent_different_increment_pairs': len(pairs),
        'single_pair_swap_cost_histogram': dict(sorted(Counter(cost([j]) for j in range(len(pairs))).items())),
        'global_pair_classes': classes, 'global_pair_class_swap_costs': masks,
        'scope': 'Syntax-level cost audit. Sharing cost is not compiled-state cost; perturbations are not certified program changes.'
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('program', type=Path)
    ap.add_argument('--output', type=Path)
    a = ap.parse_args()
    text = json.dumps(audit(a.program), indent=2) + '\n'
    if a.output:
        a.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
