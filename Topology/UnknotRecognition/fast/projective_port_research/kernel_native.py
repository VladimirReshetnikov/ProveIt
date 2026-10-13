"""Equivalent complete native, historical filtered and kernel-filtered workloads."""
from collections import Counter
from hashlib import sha256
import sys

from .common import ROOT, compile_two_block, source_hashes
from .filtered_native import workload as baseline, encode, save
from .native import cases, anchors, sector_source, checked_candidate, _prepare, euler
from .kernel_atlas import KernelFilteredAtlas


def hashes():
    result = source_hashes()
    for name in ('source_kernel.py', 'source_kernel_verify.py'):
        p = ROOT/'fast/fastunknot'/name
        result[str(p.relative_to(ROOT))] = sha256(p.read_bytes()).hexdigest()
    return result


def workload(case, arm):
    if arm != 'kernel':
        return baseline(case, arm)
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

    p = KernelFilteredAtlas(compile_two_block(source, range(source.n-7)))
    stats = dict(p.intrinsic.prepared.stats,
                 intrinsic_dimension=p.intrinsic.reduction.dimension,
                 local_kernels=p.intrinsic.prepared.local_kernel_stats)
    answers = []
    for zeros in anchors(prepared):
        result = p.search(cost, inspect, zeros=zeros)
        if result['status'] == 'INCONCLUSIVE':
            raise ArithmeticError(result)
        answers.append(dict(zeros=zeros, result=result))
    return dict(answers=answers, stats=stats, unique_inspections=len(cache), forbidden=forbidden)


def main():
    output = dict(passed=False, records=[], source_sha256=hashes(),
        scope='complete positive extreme-ray queries with independent essential-disc inspection in 22 supplied sectors; no knot-diagram provenance')
    summary = Counter()
    for case in cases():
        results = {a:workload(case, a) for a in ('native', 'filtered', 'kernel')}
        target = [a['result']['status'] for a in results['native']['answers']]
        for arm in ('filtered', 'kernel'):
            if [a['result']['status'] for a in results[arm]['answers']] != target:
                raise ArithmeticError((case['id'], arm, 'different complete answers'))
        for a in results['kernel']['answers']:
            summary[a['result']['status']] += 1
            for key in ('queries', 'transitions'):
                summary[key] += a['result'][key]
            summary['rejected'] += len(a['result']['rejected'])
        output['records'].append(dict(**case, results=results))
        save(sys.argv[1], output)
        print(case['id'], dict(summary), flush=True)
    output.update(passed=True, summary=dict(summary))
    save(sys.argv[1], output)


if __name__ == '__main__':
    main()
