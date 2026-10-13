#!/usr/bin/env python3
"""Reproduce compressed algebra benchmarks; no geometric inputs are inferred.

Run with --fast-root pointing to the patched fast/ directory.  Every positive
result is replayed in a separately built arena by the independent checker.
Wall times are observations; asymptotic statements in the article are proved.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import statistics
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_root.resolve()))
    from fastunknot.compressed_words import CompressedLimit, WordArena
    from fastunknot.cyclic_basis import cyclic_basis_blocks
    from fastunknot.cyclic_basis_verify import verify_cyclic_basis
    from fastunknot.signed_annulus_basis import compile_signed_quotient
    from fastunknot.signed_annulus_basis_verify import _quotient_words

    def arena():
        return WordArena(max_nodes=1000000, max_work=10000000)

    def build(kind, parameter, target, independent=False):
        if kind == 'fibonacci_pair':
            a, b = target.letter(1), target.letter(2)
            for _ in range(parameter):
                a, b = target.concat(a, b), a
            return [a, b], [1, 2]
        if kind == 'binary_shear_pair':
            a, b = target.letter(1), target.letter(2)
            return [a, target.concat(target.power(a, 1 << parameter), b)], [1, 2]
        if kind == 'independent_blocks':
            roots, labels = [], list(range(1, 2 * parameter + 1))
            for j in range(parameter):
                a, b = target.letter(2*j + 1), target.letter(2*j + 2)
                for _ in range(8):
                    a, b = target.concat(a, b), a
                roots.extend((a, b))
            return roots, labels
        if kind == 'triangular_transport':
            # g_i = g_(i+1)^2, ending in b.  Passive curve a*g_0.
            # This is algebraic source data only, not a certified 3-manifold.
            chain = list(range(3, parameter + 3)) + [2]
            packet = dict(method='column_leaf',
                active=[dict(two_handle=i, word=[chain[i], -chain[i+1], -chain[i+1]])
                        for i in range(parameter)],
                passive=[dict(word=[1, chain[0]])],
                components=[dict(generators=[1, 2] + chain[:-1],
                                 surviving_generators=[1, 2])],
                cancellations=[[i, chain[i]] for i in range(parameter)])
            compiler = _quotient_words if independent else compile_signed_quotient
            return compiler(target, packet), [1, 2]
        raise ValueError(kind)

    grid = {
        'fibonacci_pair': [4, 8, 16, 32, 64, 128, 512, 2048],
        'binary_shear_pair': [8, 32, 128, 512, 2048],
        'independent_blocks': [1, 4, 16, 64],
        'triangular_transport': [8, 32, 128, 512, 2048],
    }
    if args.quick:
        grid = {key: values[:3] for key, values in grid.items()}
    results = []
    for kind, parameters in grid.items():
        for parameter in parameters:
            times, verify_times, build_times = [], [], []
            record = dict(family=kind, parameter=parameter, repetitions=args.repeats)
            try:
                for _ in range(args.repeats):
                    a = arena()
                    start = time.perf_counter()
                    roots, labels = build(kind, parameter, a)
                    build_times.append(time.perf_counter() - start)
                    source_nodes = len(a.rules) - 1
                    source_reachable_nodes = len(a._reachable(roots))
                    total_length = sum(a.lengths[x] for x in roots)
                    start = time.perf_counter()
                    result = cyclic_basis_blocks(a, roots, labels)
                    times.append(time.perf_counter() - start)
                    if result['status'] != 'COMPLETE':
                        raise AssertionError(result)
                    v = arena()
                    vr, vl = build(kind, parameter, v, independent=True)
                    start = time.perf_counter()
                    valid = verify_cyclic_basis(v, vr, vl, result['certificate'])
                    verify_times.append(time.perf_counter() - start)
                    if not valid:
                        raise AssertionError('independent replay failed')
                    record.update(status='COMPLETE', verified=True,
                        expanded_total_length=str(total_length),
                        expanded_length_bits=total_length.bit_length(),
                        source_nodes=source_nodes,
                        source_reachable_nodes=source_reachable_nodes,
                        producer_nodes=len(a.rules)-1,
                        verifier_nodes=len(v.rules)-1,
                        generator_count=len(labels), root_count=len(roots),
                        nielsen_moves=len(result['certificate']['moves']),
                        certificate_json_bytes=len(json.dumps(result['certificate'],
                                                               separators=(',', ':')).encode()),
                        producer_work=a.stats['work'], verifier_work=v.stats['work'])
                record.update(build_seconds_median=statistics.median(build_times),
                    producer_seconds_median=statistics.median(times),
                    verifier_seconds_median=statistics.median(verify_times),
                    producer_seconds_samples=times, verifier_seconds_samples=verify_times)
            except CompressedLimit as error:
                record.update(status='BUDGET', detail=str(error))
            results.append(record)
            print(json.dumps({key: value for key, value in record.items()
                              if key not in ('expanded_total_length',
                                             'producer_seconds_samples',
                                             'verifier_seconds_samples')}), flush=True)
            if record['status'] == 'BUDGET':
                # Larger sizes in this family need a fresh performance study.
                break
    files = ['compressed_words.py', 'cyclic_basis.py', 'cyclic_basis_verify.py',
             'signed_annulus_basis.py', 'signed_annulus_basis_verify.py']
    hashes = {name: hashlib.sha256((args.fast_root/'fastunknot'/name).read_bytes()).hexdigest()
              for name in files}
    output = dict(schema='signed-annulus-compression-benchmarks-v1',
        created_utc=datetime.now(timezone.utc).isoformat(),
        environment=dict(python=sys.version, platform=platform.platform(),
                         processor=platform.processor()),
        caps=dict(max_nodes=1000000, max_work=10000000),
        production_sha256=hashes, results=results,
        interpretation=['No expanded word is materialized.',
                        'These are algebraic benchmarks, not native knot instances.',
                        'Producer excludes source grammar construction; verifier excludes reconstruction.',
                        'Budgets mean no conclusion; finite timings do not prove a complexity bound.'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')


if __name__ == '__main__':
    main()
