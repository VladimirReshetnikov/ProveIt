"""Whole-query representation switching and matched letter-cap capacity audit."""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize
from fastunknot.group_certificate import group_decide


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows, corpus = random.Random(2693), [], list(cases())
    arms = ('explicit', 'control', 'adaptive-cap', 'adaptive-4096', 'compressed')
    for name, diagram in corpus:
        samples = []
        for repetition in range(6):
            order, measurements = list(arms), {}
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                    group_relators=True, group_adaptive=arm.startswith('adaptive'),
                    group_switch_letters=4096 if arm == 'adaptive-4096' else None,
                    group_compressed_search=arm == 'compressed',
                    group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                group = result.evidence.get('group', {})
                measurements[arm] = dict(seconds=perf_counter()-start, status=result.status,
                    method=result.method, search_backend=group.get('search_backend'),
                    verification_backend=group.get('verification_backend'),
                    search_stats=group.get('search_stats'))
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        row = dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms})
        print(name, row['median_seconds'], flush=True)
        rows.append(row)
    capacity = []
    by_name = dict(corpus)
    for name, cap in (('survivor-00', 64), ('survivor-02', 60), ('gordian', 4096), ('gordian', 8192)):
        diagram, samples = by_name[name], []
        for repetition in range(6):
            order, measurements = ['explicit', 'control', 'adaptive', 'compressed'], {}
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                result = group_decide(Diagram.from_pd(diagram.pd), seconds=15, max_letters=cap,
                    max_work=20000000, relator_moves=True, adaptive_search=arm == 'adaptive',
                    compressed_search=arm == 'compressed')
                measurements[arm] = dict(seconds=perf_counter()-start, status=result['status'],
                    reason=result.get('reason'), search_backend=result['search_backend'],
                    verification_backend=result.get('verification_backend'), search_stats=result['search_stats'])
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        capacity.append(dict(name=name, max_letters=cap, pd=diagram.pd, samples=samples))
        print('capacity', name, cap,
              {arm: (measurements[arm]['status'], median(s['measurements'][arm]['seconds'] for s in samples))
               for arm in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        seed=2693, measured_rounds=5, excluded_warmups=1,
        group_seconds=15, global_seconds=18, max_work=20000000,
        max_letters=200000, max_nodes=100000, max_objects=50000,
        whole_query_scope='Fresh PD validation, complete recognition and independent certificate replay',
        capacity_scope='Fresh PD validation and group stage including replay, with matched reduced letter caps',
        censoring='INCONCLUSIVE is a censored group probe, not completed recognition; do not compute speedup ratios against it',
        rows=rows, capacity=capacity), indent=2)+'\n')


if __name__ == '__main__':
    main()
