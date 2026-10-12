"""Reproducible hierarchy audit and separate ordering/kernel measurements.

Run from fast/: python -B audit_separator_orders.py --output results/FILE.json
The independent checker uses union-find, not the production graph traversals.
All inputs and certificates are retained; timer limits are censored outcomes.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.filters import FilterLimit, jones_obstruction
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order, order_profile
from fastunknot.potts_exact import potts_exact
from fastunknot.separator_order import separator_scan_order, width_bounded_scan_order
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tests'))
from disk_grid import descending_grid


def independent_check(pd, certificate):
    owners = defaultdict(list)
    for v, row in enumerate(pd):
        for label in row:
            owners[label].append(v)
    assert all(len(ends) == 2 for ends in owners.values())
    edges = list(owners.values())
    def components(vertices):
        parent = {v: v for v in vertices}
        def find(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        for u, v in edges:
            if u in parent and v in parent:
                parent[find(u)] = find(v)
        parts = defaultdict(set)
        for v in vertices:
            parts[find(v)].add(v)
        return {frozenset(part) for part in parts.values()}
    seen, order = set(), []
    def visit(node):
        own = node.get('leaf', node.get('separator'))
        assert not seen.intersection(own) and len(set(own)) == len(own)
        seen.update(own)
        children = [visit(child) for child in node.get('children', [])]
        vertices = set(own).union(*(part for part, _ in children))
        if 'leaf' in node:
            assert 0 < len(own) <= certificate['leaf_size']
        else:
            from math import isqrt
            assert len(own) <= 8*(isqrt(len(vertices)-1)+1)+6
            assert all(2*len(part) <= len(vertices) for part, _ in children)
            assert components(vertices-set(own)) == {frozenset(part) for part, _ in children}
        order.extend(own)
        return vertices, 4*len(own)+max((bound for _, bound in children), default=0)
    roots = [visit(node) for node in certificate['forest']]
    assert seen == set(range(len(pd)))
    assert components(seen) == {frozenset(part) for part, _ in roots}
    assert order == certificate['order']
    frontier, widths = set(), [0]
    for v in order:
        for label in pd[v]:
            frontier.symmetric_difference_update((label,))
        widths.append(len(frontier))
    assert [max(widths), sum(widths)] == certificate['profile']
    assert certificate['width_bound'] == max((bound for _, bound in roots), default=0)
    assert max(widths) <= certificate['width_bound']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    rng = random.Random(2620)
    inputs = []
    while len(inputs) < 100:
        strands = rng.randrange(2, 7)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 45))]
        try:
            d = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        pd = list(d.pd)
        rng.shuffle(pd)
        labels = sorted({label for row in pd for label in row})
        renamed = dict(zip(labels, rng.sample(range(-10000, 10000), len(labels))))
        pd = [tuple(renamed[label] for label in row) for row in pd]
        inputs.append((f'random-{len(inputs)}', pd))
    inputs += [(f'grid-{m}', descending_grid(m)) for m in (4, 8, 16, 32)]
    inputs += [(f'tree-{h}', tree_medial(h).pd) for h in range(3, 10)]
    inputs += [('long-braid', Diagram.from_braid(2, [1]*513).pd),
               ('empty', []), ('disconnected-loops', [(0, 0, 1, 1), (2, 2, 3, 3)])]
    audit = []
    for name, pd in inputs:
        certificate = separator_scan_order(pd, leaf_size=rng.randrange(1, 9))
        independent_check(pd, certificate)
        audit.append(dict(name=name, pd=pd, certificate=certificate))
    measurements = []
    for name, pd in inputs[100:-3]:
        variants = {'greedy': lambda: best_scan_order(pd, tries=12),
                    'bounded': lambda: width_bounded_scan_order(pd)}
        for run in variants.values():
            run()  # excluded warm-up
        samples = {key: [] for key in variants}
        for _ in range(5):
            keys = list(variants)
            rng.shuffle(keys)
            for key in keys:
                start = perf_counter()
                value = variants[key]()
                samples[key].append(perf_counter()-start)
        greedy = best_scan_order(pd, tries=12)
        bounded = width_bounded_scan_order(pd)
        measurements.append(dict(name=name, n=len(pd), seconds=samples,
                                 median_seconds={k: median(v) for k, v in samples.items()},
                                 greedy_profile=order_profile(pd, greedy),
                                 bounded=bounded))
    kernels = []
    # These deliberately simple unknot diagrams stress ordering, not recognition.
    # Timing excludes preparation; full pipeline benefits must be measured separately.
    for h in (4, 5, 6, 7):
        d = tree_medial(h)
        orders = {'greedy': best_scan_order(d.pd, tries=12),
                  'bounded': width_bounded_scan_order(d.pd)['order']}
        variants = [(kind, key) for kind in ('matching', 'potts') for key in orders]
        for round_index in range(4):
            rng.shuffle(variants)
            for kind, key in variants:
                start = perf_counter()
                def check():
                    if perf_counter()-start > 2:
                        raise ScanLimit('two-second kernel allowance')
                stats = {}
                try:
                    options = dict(order=orders[key], max_states=4096,
                                   max_transitions=200000, check=check)
                    if kind == 'matching':
                        result = jones_obstruction(d, **options)
                        status = 'KNOTTED' if result is not None else 'INCONCLUSIVE'
                    else:
                        result = potts_exact(d, statistics=stats, **options)
                        status = 'KNOTTED' if result['differs'] else 'INCONCLUSIVE'
                    assert status == 'INCONCLUSIVE'
                except (FilterLimit, ScanLimit) as error:
                    status = 'LIMIT'
                    stats = dict(reason=str(error))
                elapsed = perf_counter()-start
                if round_index:
                    kernels.append(dict(height=h, n=d.crossings, kernel=kind, order=key,
                                        round=round_index, status=status, seconds=elapsed,
                                        statistics={k: v for k, v in stats.items()
                                                    if k not in ('partition_function', 'unknot_partition')}))
    sources = ['audit_separator_orders.py', 'separator_research/graphs.py',
               'fastunknot/separator_order.py', 'fastunknot/separator_potts.py',
               'fastunknot/filters.py', 'fastunknot/potts_exact.py']
    result = dict(seed=2620, input_audits=audit, ordering=measurements, kernels=kernels,
                  source_sha256={path: sha256((ROOT/path).read_bytes()).hexdigest() for path in sources},
                  scope='Ordering preparation and isolated scalar kernels; not recognition timing. '
                        'Warm-ups excluded; ordering five rounds, kernels three shuffled rounds. '
                        'Limits are censored; equal scalar values are inconclusive.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(audited=len(audit), ordering_cases=len(measurements),
                          kernel_samples=len(kernels), output=str(args.output))))


if __name__ == '__main__':
    main()
