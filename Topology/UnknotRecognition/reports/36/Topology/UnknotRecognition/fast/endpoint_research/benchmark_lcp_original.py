"""Paired audit of endpoint AP certificates, including unaccelerated controls.

Run from fast/: python benchmark_compressed_endpoint.py --output results/endpoint_ap_20261008.json
The archived baseline is the exact compressed_lcs.py at BASELINE_COMMIT; both
arms share the current word arena and all other query/replay code.
"""
import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from unittest.mock import patch

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize, compressed_lcs, compressed_overlap, compressed_search
from fastunknot.compressed_words import CompressedLimit, WordArena


ROOT = Path(__file__).resolve().parent
BASELINE_COMMIT = '38e65c9c2e2bfd42b9f71f1a1a7af15a3f8a3005'
BASELINE_FILE = ROOT/'endpoint_research/baseline_compressed_lcs.py'


def baseline_class():
    name = 'fastunknot._endpoint_ap_archived_baseline'
    spec = importlib.util.spec_from_file_location(name, BASELINE_FILE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.CommonSubstring


def validate_progressions(answer, first, step, count):
    """An independent containment/cardinality oracle for one expected AP.

    The tested implementations emit disjoint AP ranges on these families.
    Containment plus disjointness and equal cardinality proves full equality
    without enumerating any large occurrence count.
    """
    total, previous = 0, -1
    final = first+step*(count-1)
    for start, difference, size in sorted(answer):
        assert size > 0 and difference >= 0
        end = start+difference*(size-1)
        assert previous < start <= end <= final
        assert start >= first and (start-first) % step == 0
        assert size == 1 or (difference > 0 and difference % step == 0)
        total += size
        previous = end
    assert total == count


def kernel(arena, factory, family, bits):
    n = 1 << bits
    if family in ('full-overlap-control', 'phase-prefix'):
        if family == 'full-overlap-control':
            root = arena.power(arena.from_word([1, 2]), n)
            answer = factory(arena).overlaps(root, root)
            expected = (2, 2, n)
        else:
            prefix = arena.concat(arena.power(arena.from_word([3, 1, 2]), n-1), arena.letter(3))
            x = arena.concat(arena.from_word([8, 8]), prefix)
            y = arena.concat(prefix, arena.from_word([9, 9]))
            answer = factory(arena).overlaps(x, y)
            expected = (1, 3, n)
        return answer, expected, False
    core = [2, 1] if family == 'bigram-power' else [1, 2]
    tail = [1] if family == 'bigram-power' else [1, 1] if family == 'fourgram-power' else [3]
    block = arena.concat(arena.power(arena.from_word(core), n), arena.from_word(tail))
    period = arena.lengths[block]
    copies = 17 if family == 'sparse-17-control' else 65 if family == 'markers-65' else n
    x = y = arena.power(block, copies)
    expected = (period, period, copies)
    if family == 'nonperiodic-target':
        x = arena.concat(arena.power(arena.letter(4), period), arena.power(block, copies-1))
        expected = period, period, copies-1
    elif family == 'period-reject':
        damaged = arena.concat(arena.concat(arena.power(arena.from_word([1, 2]), n//2),
                                            arena.from_word([4, 4])),
                               arena.concat(arena.power(arena.from_word([1, 2]), n//2-1),
                                            arena.letter(3)))
        pair = arena.concat(block, damaged)
        x = y = arena.power(pair, 65)
        expected = 2*period, 2*period, 65
    answer = factory(arena).overlaps(x, y)
    return answer, expected, family == 'fourgram-power'


def operation(arena, factory, family, bits):
    n = 1 << bits
    if family == 'quotient-control':
        roots = [arena.power(arena.letter(1), n), arena.power(arena.letter(1), n*n+1)]
        moves = []
        assert compressed_search._search(arena, roots, {1, 2}, moves,
                                         relator_moves=True, max_letters=0)
        assert len(moves) == 2
        return moves
    block = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(3))
    run = arena.power(block, n)
    length = arena.lengths[run]
    if family.endswith('phase'):
        p = arena.lengths[block]
        shifted = arena.concat(arena.slice(block, 1, p), arena.slice(block, 0, 1))
        other = arena.power(shifted, n)
        expected = length-1
    else:
        other, expected = run, length
    if family.startswith('lcs'):
        if family.endswith('phase'):
            answer = factory(arena).longest(run, other)
        else:
            x = arena.concat(arena.concat(arena.letter(4), run), arena.letter(5))
            y = arena.concat(arena.letter(5), arena.concat(other, arena.letter(4)))
            answer = factory(arena).longest(x, y)
        assert answer[0] == expected
        return answer
    roots = [arena.concat(arena.concat(arena.letter(4), run), arena.letter(5)),
             arena.concat(arena.letter(5), arena.concat(other, arena.letter(4)))]
    assert compressed_overlap.whole_donor_move(arena, roots) is None
    move = compressed_overlap.cyclic_overlap_move(arena, roots)
    assert move is not None and move['overlap'] == expected
    compressed_overlap.apply_cyclic_overlap(arena, roots, move)
    return move


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--bits', type=int, nargs='+', default=[8, 32, 500])
    parser.add_argument('--skip-knots', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1 or any(bits < 3 for bits in args.bits):
        parser.error('positive rounds and bit parameters at least 3 are required')
    rng = random.Random(202610081)
    factories = {'baseline': baseline_class(), 'endpoint': compressed_lcs.CommonSubstring}

    @contextmanager
    def environment(arm):
        with patch.object(compressed_lcs, 'CommonSubstring', factories[arm]):
            yield factories[arm]

    families = ('markers-65', 'marker-power', 'bigram-power', 'fourgram-power',
                'phase-prefix', 'nonperiodic-target', 'period-reject',
                'full-overlap-control', 'sparse-17-control')
    kernels, operations, rows = [], [], []
    for kind, names, destination in (
            ('kernel', families, kernels),
            ('operation', ('lcs-shared-control', 'relator-shared-control', 'quotient-control',
                           'lcs-phase', 'relator-phase'), operations)):
        for family in names:
            for bits in args.bits:
                samples = []
                for repetition in range(args.rounds+1):
                    order, measurements = ['baseline', 'endpoint'], {}
                    rng.shuffle(order)
                    for arm in order:
                        with environment(arm) as factory:
                            start = perf_counter()
                            arena = WordArena(max_work=2000000, max_nodes=100000)
                            try:
                                if kind == 'kernel':
                                    answer, expected, short_one = kernel(arena, factory, family, bits)
                                else:
                                    answer = operation(arena, factory, family, bits)
                                elapsed = perf_counter()-start
                                status, reason = 'COMPLETE', None
                            except CompressedLimit as exc:
                                elapsed = perf_counter()-start
                                answer, status, reason = None, 'LIMIT', str(exc)
                        if status == 'COMPLETE' and kind == 'kernel':
                            if short_one:
                                assert (1, 0, 1) in answer
                                validate_progressions([ap for ap in answer if ap != (1, 0, 1)], *expected)
                            else:
                                validate_progressions(answer, *expected)
                        measurements[arm] = dict(seconds=elapsed, status=status, reason=reason,
                            answer=answer, nodes=len(arena.rules)-1, stats=arena.stats.copy())
                    if repetition:
                        samples.append(dict(order=order, measurements=measurements))
                row = dict(family=family, bits=bits, samples=samples,
                    median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                                    for arm in factories})
                destination.append(row)
                print(kind, family, bits,
                    {arm: (measurements[arm]['status'], row['median_seconds'][arm],
                           measurements[arm]['stats'].get('lcs_endpoint_hits', 0)) for arm in factories},
                    flush=True)
    if not args.skip_knots:
        for name, diagram in cases():
            samples = []
            for repetition in range(args.rounds+1):
                order, measurements = ['baseline', 'endpoint'], {}
                rng.shuffle(order)
                for arm in order:
                    with environment(arm):
                        start = perf_counter()
                        result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                            group_compressed_search=True, group_relators=True,
                            group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                        elapsed = perf_counter()-start
                    group = result.evidence.get('group', {})
                    assert result.status == 'UNKNOT'
                    measurements[arm] = dict(seconds=elapsed, status=result.status, method=result.method,
                        search_stats=group.get('search_stats'), certificate_sha256=hashlib.sha256(
                            json.dumps(group.get('certificate'), sort_keys=True).encode()).hexdigest())
                assert len({v['certificate_sha256'] for v in measurements.values()}) == 1
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            rows.append(dict(name=name, pd=diagram.pd, samples=samples,
                median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                                for arm in factories}))
            print('knot', name, rows[-1]['median_seconds'], flush=True)
    digest_paths = [BASELINE_FILE, ROOT/'fastunknot/compressed_endpoint.py',
                    ROOT/'fastunknot/compressed_lcs.py', ROOT/'fastunknot/compressed_words.py',
                    Path(__file__)]
    payload = dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE_COMMIT, source_sha256={str(p.relative_to(ROOT)):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in digest_paths},
        seed=202610081, measured_rounds=args.rounds, excluded_warmups=1,
        kernel_max_work=2000000, max_nodes=100000, group_max_work=20000000,
        comparison='Exact archived LCS module versus endpoint-AP module, common current arena and replay code',
        kernel_scope='Fresh arena construction plus complete suffix/prefix overlap query; independent AP oracle outside clock',
        operation_scope='Fresh construction plus LCS or whole-donor rejection, cyclic overlap and exact producer application; no knot verdict',
        knot_scope='Fresh PD reconstruction removes braid provenance; complete recognition and independent certificate replay',
        censoring='LIMIT is incomplete, never a negative answer or a completed-time denominator',
        caveat='An inner string-query improvement is not an asymptotic improvement for complete knot recognition; report activation counts',
        kernels=kernels, operations=operations, rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    main()
