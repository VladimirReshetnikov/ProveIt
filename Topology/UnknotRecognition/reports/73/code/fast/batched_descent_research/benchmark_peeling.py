"""Paired complete-census peeled scoring, against full individual replay.

Both arms include their own source preparation.  The fast arm constructs
the dynamic index from scratch.  The reference executes every candidate
with the established single-move producer/consumer and recomputes all
vertex-link minima.  This measures scores, not recognition or a policy race.
"""
import argparse
import json
from pathlib import Path
import platform
from statistics import median
import time

from fastunknot.cocycle_peeling import CocyclePeelingState
from fastunknot.cocycle_peeling_verify import _summary
from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner_batch import pachner_32_regions


def indexed(raw, heights, check):
    state = CocyclePeelingState(raw, heights, check=check)
    result = state.score_candidates()
    return [(c['tetrahedron'], c['vertices'],
             c['peeling']['peeled_euler_gain'], c['peeling']['peeled_piece_saving'])
            for c in result['candidates']]


def literal(raw, heights, check):
    candidates = pachner_32_regions(raw, heights, check=check)['candidates']
    before = _summary(raw, heights, check)
    output = []
    for candidate in candidates:
        check()
        move = pachner_32(raw, candidate['tetrahedron'], candidate['vertices'], check=check)
        transported = transport_cocycle(raw, heights, move['triangulation'],
                                        move['certificate'], check=check)
        after = _summary(move['triangulation'], transported['heights'], check)
        gain = after['euler']-before['euler']-after['link_euler']+before['link_euler']
        saving = before['pieces']-after['pieces']+after['link_pieces']-before['link_pieces']
        output.append((candidate['tetrahedron'], candidate['vertices'], gain, saving))
    return output


def timed(function, raw, heights):
    callbacks = 0
    def tick():
        nonlocal callbacks
        callbacks += 1
    start = time.perf_counter()
    answer = function(raw, heights, tick)
    return answer, time.perf_counter()-start, callbacks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--sizes', type=int, nargs='+', default=[1, 4, 8, 16, 32, 64])
    parser.add_argument('--families', nargs='+', default=['layered', 'unknot'])
    args = parser.parse_args()
    report = dict(schema='peeled-census-paired-v1', python=platform.python_version(),
        platform=platform.platform(), rounds=args.rounds,
        scope='Fresh index plus complete census versus full individual geometric replay.', cases=[])
    for family in args.families:
        for size in args.sizes:
            source_path = args.evidence / f'{family}-{size}.json'
            source = json.loads(source_path.read_text())
            raw, heights = source['before'], source['heights']
            samples = []
            for repetition in range(args.rounds):
                pair = {}
                for name in (('indexed', 'literal') if repetition % 2 == 0 else ('literal', 'indexed')):
                    answer, elapsed, callbacks = timed(globals()[name], raw, heights)
                    pair[name] = dict(answer=answer, seconds=elapsed, callbacks=callbacks)
                if pair['indexed']['answer'] != pair['literal']['answer']:
                    raise ArithmeticError('complete per-site peeled outputs disagree')
                samples.append({name:{k:v for k,v in value.items() if k != 'answer'}
                                for name,value in pair.items()})
            fast = median(s['indexed']['seconds'] for s in samples)
            slow = median(s['literal']['seconds'] for s in samples)
            case = dict(family=family, inserted_regions=size, tetrahedra=len(raw['tetrahedra']),
                candidates=len(answer), exact_outputs_equal=True, indexed_seconds=fast,
                literal_seconds=slow, speedup=slow/fast, samples=samples,
                source_evidence=source_path.name)
            report['cases'].append(case)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            print(f'{family} k={size}: t={case["tetrahedra"]}, sites={case["candidates"]}, '
                  f'{slow/fast:.2f}x; exact agreement', flush=True)


if __name__ == '__main__':
    main()
