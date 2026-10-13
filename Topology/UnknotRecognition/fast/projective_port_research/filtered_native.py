"""Complete essential-disc candidate search in the 22 retained sectors."""
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import sys

from .common import compile_two_block, source_hashes
from .filtered import FilteredAtlas
from .native import (cases, anchors, sector_source, checked_candidate, _prepare,
                     euler, matching, build_sector_kernel, sector_rays)
from experiments.oracle import all_rays


def encode(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, (set, frozenset)):
        return sorted(value)
    raise TypeError(type(value).__name__)


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, default=encode)+'\n')


def workload(case, arm):
    tri = case['triangulation']
    prepared = _prepare(tri, lambda: None)
    source, forbidden = sector_source(tri, case['support'])
    cost = euler(tri)
    cache = {}
    def inspect(x):
        key = tuple(x)
        if key not in cache:
            c = checked_candidate(tri, prepared, source, cost, x, ())
            cache[key] = dict(accepted=c['contains_compressing_disk'], certificate=c)
        return cache[key]
    if arm == 'filtered':
        p = FilteredAtlas(compile_two_block(source, range(source.n-7)), ray_method='zeros')
        stats = dict(p.intrinsic.prepared.stats,
                     intrinsic_dimension=p.intrinsic.reduction.dimension)
    elif arm == 'native':
        kernel = build_sector_kernel(tri, case['support'])
        stats = {}
        rays = [tuple(v for row in rows for v in row) for rows in sector_rays(kernel, stats=stats)]
    else:
        raise ValueError('unknown arm')
    answers = []
    for zeros in anchors(prepared):
        if arm == 'filtered':
            result = p.search(cost, inspect, zeros=zeros)
            assert result['status'] != 'INCONCLUSIVE', result
        else:
            trace = []
            for x in rays:
                if any(x[j] for j in zeros) or sum(a*b for a,b in zip(cost,x)) <= 0:
                    continue
                trace.append(dict(coordinates=x, evidence=inspect(x)))
                if trace[-1]['evidence']['accepted']:
                    break
            result = dict(status='ACCEPTED_EXTREME' if trace and trace[-1]['evidence']['accepted']
                          else 'NO_ACCEPTED_EXTREME', trace=trace)
        answers.append(dict(zeros=zeros, result=result))
    return dict(answers=answers, stats=stats, unique_inspections=len(cache), forbidden=forbidden)


def main():
    output = dict(passed=False, records=[], source_sha256=source_hashes(),
        scope='complete accepted positive extreme-ray queries in the stated sectors and anchor faces; supplied triangulations only')
    oracle_cache = {}
    summary = Counter()
    for case in cases():
        results = {a:workload(case, a) for a in ('native', 'filtered')}
        target = [a['result']['status'] for a in results['native']['answers']]
        assert [a['result']['status'] for a in results['filtered']['answers']] == target
        independent = False
        if len(case['triangulation']['tetrahedra']) == 2:
            tri = case['triangulation']
            if not oracle_cache:
                source = matching(tri)
                prepared = _prepare(tri, lambda: None)
                cost = euler(tri)
                for r in all_rays(source.n, source.equations, source.conflicts):
                    if sum(a*b for a,b in zip(r,cost)) > 0:
                        c = checked_candidate(tri, prepared, source, cost, r, ())
                        oracle_cache[tuple(r)] = c['contains_compressing_disk']
            forbidden = results['filtered']['forbidden']
            expected = ['ACCEPTED_EXTREME' if any(yes and not any(r[j] for j in tuple(a['zeros'])+tuple(forbidden))
                        for r,yes in oracle_cache.items()) else 'NO_ACCEPTED_EXTREME'
                        for a in results['filtered']['answers']]
            assert expected == target
            independent = True
        for a in results['filtered']['answers']:
            summary[a['result']['status']] += 1
            summary['queries'] += a['result']['queries']
            summary['rejected'] += len(a['result']['rejected'])
            summary['transitions'] += a['result']['transitions']
        output['records'].append(dict(**case, results=results, independent_source_oracle=independent))
        save(sys.argv[1], output)
        print(case['id'], dict(summary), flush=True)
    output.update(passed=True, summary=dict(summary))
    save(sys.argv[1], output)


if __name__ == '__main__':
    main()
