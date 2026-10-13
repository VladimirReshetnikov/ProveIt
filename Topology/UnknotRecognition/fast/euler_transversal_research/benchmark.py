"""Paired bounded diagram queries: ordinary DFS and conflict learning.

All native construction, search (including failed candidates and subset
filtering), internal replay and full-result serialization are timed. Imports,
diagram objects and separate independent warmup verification are excluded.
The bounded figure-eight DFS query is inconclusive; its elapsed-time ratio
compares different outcomes and is not a speedup between two recognitions.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
from random import Random
from statistics import median
import sys
from time import perf_counter_ns

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from euler_crushing_research.benchmark import encode_result, verify_result
from .common import DIAGRAM_CONFIG, source_hashes


SEED = 2026101207
ARMS = ('tree', 'transversal')


def configs():
    return {arm: dict(DIAGRAM_CONFIG, sector_method=arm) for arm in ARMS}


def cases():
    return [('circle', Diagram.from_pd([])),
            ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
            ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2]))]


def expected_status(name, arm):
    return ('UNKNOT' if name == 'circle' else
            'INCONCLUSIVE' if name == 'figure_eight' and arm == 'tree' else 'KNOTTED')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=5)
    parser.add_argument('--aa', type=int, default=1)
    parser.add_argument('--batch', type=int, default=1)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    configuration, rng = configs(), Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(),
        pairs=args.pairs, aa=args.aa, batch=args.batch, seed=SEED,
        python=sys.version, platform=platform.platform(), arms=ARMS,
        configs=configuration,
        scope='complete bounded diagram queries; native construction, shelling, preprocessing, all learning/restarts/subsets, discovery, internal replay and serialization timed; imports, diagram objects and independent warmup replay excluded',
        caveat='figure_eight tree is INCONCLUSIVE: its ratio compares different outcomes, not two completed recognitions',
        records=[])
    target = Path(args.output)

    def query(diagram, arm):
        result = recognize_by_crushing(diagram, **configuration[arm])
        encoded = encode_result(result)
        return result, len(encoded), sha256(encoded).hexdigest()

    def sample(diagram, arm, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result, size, digest = query(diagram, arm)
            assert digest == expected, 'timed output differs from verified warmup'
        elapsed = perf_counter_ns()-start
        return dict(ns=elapsed/args.batch, elapsed_ns=elapsed,
                    stats=result['stats'], status=result['status'],
                    result_bytes=size, output_sha256=digest)

    for name, diagram in cases():
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd],
                      warmup_results={}, warmup_sha256={},
                      samples=[], aa_samples=[])
        for arm in ARMS:
            result, _, digest = query(diagram, arm)
            assert result['status'] == expected_status(name, arm)
            replay = verify_result(diagram, result, arm)
            assert replay == ('partial_chain' if result['status'] == 'INCONCLUSIVE' else 'recognition')
            record['warmup_results'][arm] = result
            record['warmup_sha256'][arm] = digest
        for _ in range(args.pairs):
            order = list(ARMS); rng.shuffle(order)
            record['samples'].append(dict(order=order, results={arm:
                sample(diagram, arm, record['warmup_sha256'][arm]) for arm in order}))
        for _ in range(args.aa):
            order = ['A', 'B']; rng.shuffle(order)
            record['aa_samples'].append(dict(order=order, results={label:
                sample(diagram, 'tree', record['warmup_sha256']['tree']) for label in order}))
        record['median_ns'] = {arm: median(s['results'][arm]['ns'] for s in record['samples'])
                               for arm in ARMS}
        record['paired_tree_over_transversal'] = median(
            s['results']['tree']['ns']/s['results']['transversal']['ns'] for s in record['samples'])
        record['aa_ratio'] = median(s['results']['A']['ns']/s['results']['B']['ns']
                                    for s in record['aa_samples'])
        output['records'].append(record)
        target.write_text(json.dumps(output, indent=2)+'\n')
        print(name, record['median_ns'], record['paired_tree_over_transversal'],
              record['aa_ratio'], flush=True)
    assert output['source_sha256'] == source_hashes(), 'benchmarked source changed'
    output['passed'] = True
    target.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
