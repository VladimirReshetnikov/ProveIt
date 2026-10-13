"""Paired complete diagram queries: subset versus conflict-directed candidates.

Native construction, shelling, vertex reduction, candidate search, all LP work,
internal replay and full-result serialization are timed. Imports, prepared
Diagram objects and separate independent warmup replay are excluded.
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

from fastunknot.normal_crushing_search import recognize_by_crushing
from euler_crushing_research.benchmark import encode_result, verify_result
from euler_tree_research.fixtures import diagram_cases
from .common import POLICIES, SEED, configs, source_hashes


def expected_status(name):
    return 'UNKNOT' if name == 'circle' else 'KNOTTED'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=5)
    parser.add_argument('--aa', type=int, default=1)
    parser.add_argument('--batch', type=int, default=1)
    args = parser.parse_args()
    if min(args.pairs,args.aa,args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    configuration, rng = configs(), Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(),
        pairs=args.pairs, aa=args.aa, batch=args.batch, seed=SEED,
        python=sys.version, platform=platform.platform(), arms=POLICIES,
        configs=configuration,
        scope='paired complete diagram queries; native construction, shelling, preprocessing, candidate filtering and restarts, all LP work, internal replay and serialization timed; imports, Diagram objects and independent warmup replay excluded',
        validation='timed serialized output must equal the independently verified warmup; both arms must complete the same recognition outcome',
        aa_arm='subsets', records=[])
    target = Path(args.output)
    def save():
        target.write_text(json.dumps(output,indent=2)+'\n')
    save()

    def query(diagram, policy):
        result = recognize_by_crushing(diagram, **configuration[policy])
        encoded = encode_result(result)
        return result,len(encoded),sha256(encoded).hexdigest()

    def sample(diagram, policy, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result,size,digest = query(diagram,policy)
            assert digest == expected, 'timed result differs from verified warmup'
        elapsed = perf_counter_ns()-start
        return dict(ns=elapsed/args.batch, elapsed_ns=elapsed,
            stats=result['stats'],status=result['status'],result_bytes=size,output_sha256=digest)

    for name,diagram in diagram_cases():
        record = dict(id=name,input_pd=[list(row) for row in diagram.pd],
            warmup_results={},warmup_sha256={},samples=[],aa_samples=[])
        output['records'].append(record)
        for policy in POLICIES:
            result,_,digest = query(diagram,policy)
            record['warmup_results'][policy] = result
            record['warmup_sha256'][policy] = digest
            save()  # Preserve an unexpected bounded partial outcome explicitly.
            assert verify_result(diagram,result,policy) == ('partial_chain'
                if result['status'] == 'INCONCLUSIVE' else 'recognition')
            assert result['status'] == expected_status(name), (name,policy,result['status'])
        for _ in range(args.pairs):
            order = list(POLICIES)
            rng.shuffle(order)
            record['samples'].append(dict(order=order,results={policy:
                sample(diagram,policy,record['warmup_sha256'][policy]) for policy in order}))
            save()
        for _ in range(args.aa):
            order = ['A','B']
            rng.shuffle(order)
            record['aa_samples'].append(dict(order=order,results={label:
                sample(diagram,'subsets',record['warmup_sha256']['subsets']) for label in order}))
            save()
        record['median_ns'] = {policy:median(s['results'][policy]['ns'] for s in record['samples'])
                               for policy in POLICIES}
        record['paired_subsets_over_conflicts'] = median(
            s['results']['subsets']['ns']/s['results']['conflicts']['ns'] for s in record['samples'])
        record['aa_ratio'] = median(s['results']['A']['ns']/s['results']['B']['ns']
                                    for s in record['aa_samples'])
        save()
        print(name,record['median_ns'],record['paired_subsets_over_conflicts'],
              record['aa_ratio'],flush=True)
    assert output['source_sha256'] == source_hashes(), 'benchmarked sources changed'
    output['passed'] = True
    save()


if __name__ == '__main__':
    main()
