#!/usr/bin/env python3
"""Portable exact census of the pinned comparison artifacts.

This verifies the retained equation bytes against the original research receipt.
Quartic degrees are recomputed by full expansion. Compressed circuit degrees
remain claims of the separately identified inherited proofs; only their exact
live operation counts are independently recomputed here.
"""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def run():
    pins = read(ROOT / 'BASELINE_AUDIT.json')
    result = {'status': 'PASS', 'snapshot': pins['snapshot'], 'quartics': {}, 'circuits': {}}
    for label, rec in pins['quartics'].items():
        folder = ROOT / 'baselines' / label
        ep, pp = folder / 'equation.json', folder / 'expanded_polynomial.json'
        need(sha256(ep.read_bytes()).hexdigest() == rec['equation_sha256'], label + ' equation pin')
        need(sha256(pp.read_bytes()).hexdigest() == rec['expanded_sha256'], label + ' polynomial pin')
        eq, supplied = read(ep), read(pp)
        collected = defaultdict(int)
        for row in eq['residuals']:
            for a, m in row['terms']:
                for b, n in row['terms']:
                    collected[tuple(sorted(m + n))] += a * b
        collected = {m: c for m, c in collected.items() if c}
        claimed = {tuple(m): c for c, m in supplied['terms']}
        need(len(claimed) == len(supplied['terms']) and collected == claimed, label + ' every coefficient')
        metrics = dict(variables=len(eq['variables']), residuals=len(eq['residuals']),
                       monomials=len(collected), degree=max(map(len, collected)),
                       height=max(map(abs, collected.values())))
        need(all(metrics[k] == rec[k] for k in metrics), label + ' census')
        result['quartics'][label] = metrics
    for label, rec in pins['circuits'].items():
        path = ROOT / 'baselines' / (label + '.json')
        need(sha256(path.read_bytes()).hexdigest() == rec['sha256'], label + ' source pin')
        equation, live = read(path), set()
        if 'nodes' in equation:
            nodes = equation['nodes']
            def typ(node):
                return node['kind'] if isinstance(node, dict) else node[0]
            def args(node):
                return [node['left'], node['right']] if isinstance(node, dict) else node[1:]
            def visit(k):
                if k in live:
                    return
                live.add(k)
                if typ(nodes[k]) in ['add', 'sub', 'mul']:
                    for a in args(nodes[k]):
                        visit(a)
            visit(equation['output'])
            census = Counter(typ(nodes[k]) for k in live if typ(nodes[k]) in ['add', 'sub', 'mul'])
            total = len(nodes)
        else:
            registers = {row[0]: row for row in equation['source']}
            def visit(k):
                if not isinstance(k, str) or k not in registers or k in live:
                    return
                live.add(k)
                for a in registers[k][2:]:
                    visit(a)
            visit(equation['output'])
            census = Counter({'+': 'add', '-': 'sub', '*': 'mul'}[registers[k][1]] for k in live)
            total = len(registers)
        need(len(live) == total, label + ' all nodes live')
        need(dict(census) == rec['operation_counts'] and sum(census.values()) == rec['operations'], label + ' operations')
        need(equation['exact_degree'] == rec['degree'], label + ' inherited degree label')
        result['circuits'][label] = {'operations': sum(census.values()),
                                     'inherited_exact_degree': rec['degree']}
    return result


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
