"""Reproducible source-native 2/3 census audits and paired timing experiments.

Run from fast/: python core_dual_benchmark.py --output PATH --rounds 7
Use --audit-only for correctness without recording comparable timing claims.
Regina is used only by the explicit independent oracle.  The disabled native
strategy is an abstention baseline, so its runtime is not a speedup baseline.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from core_dual_fixtures import (interior_loop_torus, nested_interior_torus,
                                vertex_link_coordinates)
import fastunknot
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import (interior_vertex_torus, layered_torus, regina_surface,
                                           regina_triangulation)


def cases():
    raw, basis = interior_vertex_torus()
    samples = [dict(id='interior/empty', triangulation=raw,
                    coordinates=[[0] * 7 for _ in basis['sphere']])]
    samples += [dict(id=f'interior/{name}', triangulation=raw, coordinates=rows)
                for name, rows in basis.items()]
    for count in (2, 8, 64, 512):
        samples.append(dict(id=f'interior/mobius_{count}', triangulation=raw,
                            coordinates=[[count * x for x in row]
                                         for row in basis['mobius']]))
    loop = interior_loop_torus()
    for interior, boundary in ((0, 0), (1, 0), (0, 1), (1, 1)):
        samples.append(dict(id=f'loop/links_{interior}_{boundary}', triangulation=loop,
                            coordinates=vertex_link_coordinates(
                                loop, interior=interior, boundary=boundary)))
    for depth in (1, 2, 4, 8):
        subdivided = nested_interior_torus(depth)
        samples.append(dict(id=f'nested/{depth}/empty', triangulation=subdivided,
                            coordinates=vertex_link_coordinates(subdivided)))
    for tetrahedra, copies in ((1, 0), (4, 1), (4, 64)):
        control, meridian = layered_torus(tetrahedra)
        samples.append(dict(id=f'no_three/{tetrahedra}/{copies}', triangulation=control,
                            coordinates=[[copies * x for x in row] for row in meridian]))
    return samples


def native(case, strategy):
    start = time.perf_counter()
    result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                   record_certificate=True, dual_strategy=strategy)
    produced = time.perf_counter()
    if result['status'] == 'COMPLETE':
        assert verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                              result['certificate'])
    end = time.perf_counter()
    return result, dict(produce=produced - start, replay=end - produced, total=end - start)


def explicit(case):
    if sum(map(sum, case['coordinates'])) > 50000:
        raise ValueError('explicit normal-disc expansion cap exceeded')
    start = time.perf_counter()
    triangulation = regina_triangulation(case['triangulation'])
    surface = regina_surface(triangulation, case['coordinates'])
    cut = surface.cutAlong()
    histogram = Counter(c.recogniseHandlebody() for c in cut.triangulateComponents())
    end = time.perf_counter()
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
                cut_tetrahedra=cut.size()), end - start


def pins():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(Path(fastunknot.__file__).parent.glob('*.py'))}


def digest(value):
    data = json.dumps(json_safe(value), sort_keys=True).encode()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--audit-only', action='store_true')
    parser.add_argument('--capacity', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    import regina
    source_pins = pins()
    bank = cases()
    report = dict(source_revision='8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4',
                  native_source_sha256=source_pins, fixture_digest=digest(bank),
                  python=sys.version, platform=platform.platform(),
                  regina=regina.versionString(), seed=20261012,
                  rounds=0 if args.audit_only else args.rounds,
                  timing_meaning='explicit cut and recognition / native census production and replay',
                  disabled_meaning='abstention baseline, not a comparable successful computation',
                  cases=[], capacity=[])
    rng = random.Random(20261012)
    for case in bank:
        reference, _ = explicit(case)
        record = dict(id=case['id'], tetrahedra=len(case['coordinates']),
                      normal_discs=sum(map(sum, case['coordinates'])),
                      reference=reference, native={}, samples=[])
        for strategy in ('disabled', 'bfs', 'max_weight'):
            result, _ = native(case, strategy)
            entry = dict(status=result['status'], reason=result.get('reason'),
                         dual_stats=result['stats'].get('dual'))
            if result['status'] == 'COMPLETE':
                assert result['census']['histogram'] == reference['histogram'], (case['id'], result)
                entry.update(histogram=result['census']['histogram'],
                             certificate_digest=digest(result['certificate']))
            record['native'][strategy] = entry
        for _ in range(0 if args.audit_only else args.rounds):
            order = ['bfs', 'max_weight', 'disabled', 'explicit']
            rng.shuffle(order)
            sample = dict(order=order)
            for method in order:
                if method == 'explicit':
                    value, timing = explicit(case)
                    assert value == reference
                else:
                    result, timing = native(case, method)
                    assert result['status'] == record['native'][method]['status']
                    if result['status'] == 'COMPLETE':
                        assert result['census']['histogram'] == reference['histogram']
                sample[method] = timing
            record['samples'].append(sample)
        if record['samples']:
            record['medians'] = {method: statistics.median(s[method]['total']
                                  for s in record['samples'])
                                  for method in ('bfs', 'max_weight', 'disabled')}
            record['medians']['explicit'] = statistics.median(s['explicit'] for s in record['samples'])
            record['median_paired_ratios'] = {
                method: statistics.median(s['explicit'] / s[method]['total']
                                          for s in record['samples'])
                for method in ('bfs', 'max_weight')
                if record['native'][method]['status'] == 'COMPLETE'}
            # A/A exposes short-run timing variation using the same operation.
            aa = []
            for _ in range(3):
                _, a = explicit(case)
                _, b = explicit(case)
                aa.append(a / b)
            record.update(aa_ratios=aa, aa_median=statistics.median(aa))
        report['cases'].append(record)
        Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')
        print(json.dumps({key: value for key, value in record.items()
                          if key not in ('samples', 'aa_ratios')}), flush=True)
    if args.capacity:
        raw, basis = interior_vertex_torus()
        count = 1 << 16384
        case = dict(triangulation=raw,
                    coordinates=[[count * x for x in row] for row in basis['mobius']])
        for method in ('bfs', 'max_weight'):
            result, timing = native(case, method)
            data = dict(strategy=method, multiplicity_power=16384,
                        status=result['status'], reason=result.get('reason'), timing=timing,
                        dual_stats=result['stats'].get('dual'))
            if result['status'] == 'COMPLETE':
                data.update(histogram=result['census']['histogram'],
                            certificate_digest=digest(result['certificate']))
            report['capacity'].append(data)
    assert pins() == source_pins, 'native sources changed during benchmark'
    Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')


if __name__ == '__main__':
    main()
