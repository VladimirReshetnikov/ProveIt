"""Exact compressed-word capacity and end-to-end verification-cost audit."""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena
from fastunknot.group_certificate import group_certificate, verify_group_certificate, GroupLimit
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from test_compressed_words import inflated_certificate


def cases():
    for i, (_, strands, word) in enumerate(SURVIVORS):
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        yield f'survivor-{i:02d}', d
        if i in (3, 8):
            yield f'mirror-{i:02d}', d.mirror()
    yield 'gordian', Diagram.from_json(json.loads((ROOT/'normal_research/gordian.json').read_text()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2686), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order = ['explicit', 'control', 'compressed']
            rng.shuffle(order)
            measurements = {}
            for arm in order:
                start = perf_counter()
                d = Diagram.from_pd(diagram.pd)
                result = recognize(d, use_group=True, group_relators=True,
                    group_compressed=arm == 'compressed', group_seconds=2, group_max_work=10000000,
                    seconds=4, max_objects=50000)
                measurements[arm] = dict(seconds=perf_counter()-start, status=result.status,
                                         method=result.method, verification_backend=result.evidence.get('group', {}).get('verification_backend'))
            assert {r['status'] for r in measurements.values()} == {'UNKNOT'}
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        certificate = group_certificate(diagram, relator_moves=True, max_work=10000000)
        replay = []
        for repetition in range(6):
            order = [False, True]
            rng.shuffle(order)
            pair = {}
            for compressed in order:
                stats, start = {}, perf_counter()
                assert verify_group_certificate(diagram, certificate, compressed=compressed,
                                                max_work=10000000, stats=stats)
                pair['compressed' if compressed else 'explicit'] = dict(seconds=perf_counter()-start, stats=stats)
            if repetition:
                replay.append(pair)
        row = dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                            for arm in ('explicit', 'control', 'compressed')}, replay=replay)
        rows.append(row)
        print(name, row['median_seconds'], flush=True)
    stress = []
    for count in (8, 16, 32, 64):
        d, certificate = inflated_certificate(count)
        samples = []
        for repetition in range(6):
            order, pair = [False, True], {}
            rng.shuffle(order)
            for compressed in order:
                stats, start = {}, perf_counter()
                try:
                    valid = verify_group_certificate(d, certificate, compressed=compressed,
                                                     max_work=10000000, stats=stats)
                    assert valid
                    status, reason = 'VERIFIED', None
                except GroupLimit as exc:
                    status, reason = 'LIMIT', str(exc)
                pair['compressed' if compressed else 'explicit'] = dict(
                    seconds=perf_counter()-start, status=status, reason=reason, stats=stats)
            if repetition:
                samples.append(pair)
        stress.append(dict(iterations=count, input_crossings=d.crossings, certificate=certificate, samples=samples))
    kernels = []
    for exponent_bits in (8, 16, 32, 64, 100):
        samples = []
        for repetition in range(4):
            start, arena = perf_counter(), WordArena()
            exponent = 2**exponent_bits
            a = arena.concat(arena.power(arena.from_word([1, 2]), exponent), arena.letter(1))
            b = arena.concat(arena.letter(1), arena.power(arena.from_word([2, 1]), exponent))
            assert arena.equal(a, b)
            assert arena.reduce(arena.concat(a, arena.inverse(b))) == 0
            if repetition:
                samples.append(dict(seconds=perf_counter()-start, nodes=len(arena.rules)-1,
                                    represented_length_hex=hex(arena.lengths[a]), stats=arena.stats.copy()))
        kernels.append(dict(exponent_bits=exponent_bits, samples=samples))
    data = dict(python=sys.version, platform=platform.platform(), seed=2686,
        query_measured_rounds=5, query_excluded_warmups=1, group_seconds=2, group_max_work=10000000,
        global_seconds=4, max_objects=50000, explicit_max_letters=200000, compressed_max_nodes=100000,
        query_scope='fresh validated PD plus whole recognition, including certificate replay',
        replay_scope='same existing certificate, fresh verifier state; search excluded',
        stress_scope='deliberately inflated proofs of a three-crossing unknot; not difficult recognition instances',
        kernel_scope='noncanonical parses of (ab)^(2^k)a and a(ba)^(2^k), exact equality and cancellation',
        censoring='LIMIT records exhaustion and is not a completed verification time',
        rows=rows, stress=stress, kernels=kernels)
    args.output.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    main()
