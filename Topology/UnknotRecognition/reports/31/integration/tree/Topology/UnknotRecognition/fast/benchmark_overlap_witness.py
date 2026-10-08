"""Paired audit of optional strict-majority witnesses and cyclic extension.

The default recognizer is unchanged. The full-query arm installs the optional
helper in the existing compressed-overlap dispatch; local and residual probes
report their narrower scopes separately. Limits remain censored observations.
"""
import argparse
from contextlib import contextmanager
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from unittest.mock import patch

from benchmark_compressed_words import cases
from benchmark_whitehead_power import historical
from fastunknot import Diagram, recognize, compressed_overlap, compressed_search
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.group_certificate import (
    _Budget, _certificate_version, _presentation, _reduce, verify_group_certificate,
)
from fastunknot.relator_overlap import apply_overlap


BASELINE = '8a95834940cf77cdab1b39571ffc102ca8b6bede'
ROOT = Path(__file__).resolve().parent
TAIL = [1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3]


def residual():
    """A real Gordian residual reached by a saved independently replayable prefix."""
    record = json.loads((ROOT/'tests/fixtures/gordian_relator_power.json').read_text())
    diagram, original = Diagram.from_pd(record['pd']), record['certificate']
    index = next(i for i, move in enumerate(original['moves']) if move['kind'] == 'relator_power')
    prefix = deepcopy(original['moves'][:index])
    budget = _Budget(lambda: None, 200000, 20000000)
    alive, words = _presentation(diagram, budget)
    for move in prefix:
        if move['kind'] == 'relator':
            apply_overlap(words, move, budget, _reduce)
            continue
        assert move['kind'] == 'eliminate'
        relation, g = move['relation'], move['generator']
        word = words[relation]
        pos = next(i for i, x in enumerate(word) if abs(x) == g)
        rest = word[pos+1:]+word[:pos]
        value = [-x for x in rest[::-1]] if word[pos] > 0 else rest
        inverse = [-x for x in value[::-1]]
        words[relation] = []
        alive.remove(g)
        words = [_reduce([y for x in w for y in
                 (value if x == g else inverse if x == -g else [x])], budget) for w in words]
    return diagram, original, prefix, alive, words


def build_family(arena, family, bits):
    n = 2**bits
    if family == 'gain-tradeoff':
        words = [list(range(1, 9)),
                 list(range(1, 6))+[9, 10, 11]+list(range(1, 8))+[12]]
        return [arena.from_word(word) for word in words]
    run = arena.power(arena.from_word([1, 2]), n)
    tail = arena.from_word(TAIL)
    if family == 'prefix':
        return [arena.concat(run, arena.from_word([x]+TAIL+[y])) for x, y in ((3, 1), (1, 2))]
    if family == 'suffix':
        return [arena.concat(arena.from_word([x]+TAIL+[y]), run) for x, y in ((3, 1), (1, 2))]
    if family == 'shared-tail-control':
        return [arena.concat(run, arena.concat(arena.letter(x), tail)) for x in (3, 1)]
    assert family == 'no-majority'
    return [run, arena.power(arena.from_word([1, 1, 2, 2]), n)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--queries-only', action='store_true')
    parser.add_argument('--kernels-only', action='store_true')
    args = parser.parse_args()
    if args.rounds < 1 or args.queries_only and args.kernels_only:
        parser.error('positive rounds and at most one scope restriction are required')
    old = historical('compressed_overlap', BASELINE).cyclic_overlap_move
    current = compressed_overlap.cyclic_overlap_move

    def witness(arena, roots):
        return current(arena, roots, witness_first=True)

    @contextmanager
    def environment(arm):
        helper = witness if arm == 'witness' else old
        with patch.object(compressed_overlap, 'cyclic_overlap_move', helper):
            yield helper

    rng, rows, operations, residuals = random.Random(3110), [], [], []
    arms = ['baseline', 'control', 'witness']
    if not args.kernels_only:
        for name, diagram in cases():
            samples = []
            for repetition in range(args.rounds+1):
                order, measurements = arms[:], {}
                rng.shuffle(order)
                for arm in order:
                    with environment(arm):
                        start = perf_counter()
                        result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                            group_compressed_search=True, group_relators=True,
                            group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                        elapsed = perf_counter()-start
                    group = result.evidence.get('group', {})
                    measurements[arm] = dict(seconds=elapsed, status=result.status, method=result.method,
                        search_stats=group.get('search_stats'), certificate_sha256=hashlib.sha256(
                            json.dumps(group.get('certificate'), sort_keys=True).encode()).hexdigest())
                    assert result.status == 'UNKNOT'
                assert len({v['certificate_sha256'] for v in measurements.values()}) == 1
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            rows.append(dict(name=name, pd=diagram.pd, samples=samples,
                median_seconds={a: median(s['measurements'][a]['seconds'] for s in samples) for a in arms}))
            print(name, rows[-1]['median_seconds'], flush=True)
    if not args.queries_only:
        for family in ('prefix', 'suffix', 'shared-tail-control', 'no-majority', 'gain-tradeoff'):
            for bits in ((0,) if family == 'gain-tradeoff' else (8, 32, 500)):
                samples = []
                for repetition in range(args.rounds+1):
                    order, measurements = arms[:], {}
                    rng.shuffle(order)
                    for arm in order:
                        with environment(arm) as helper:
                            start = perf_counter()
                            arena = WordArena(max_work=2000000)
                            roots = build_family(arena, family, bits)
                            before = sum(arena.lengths[r] for r in roots)
                            move = None
                            try:
                                assert compressed_overlap.whole_donor_move(arena, roots) is None
                                move = helper(arena, roots)
                                if family == 'no-majority':
                                    assert move is None
                                else:
                                    assert move is not None
                                    if family in ('prefix', 'suffix'):
                                        assert move['overlap'] == 2*(2**bits)
                                    if family == 'shared-tail-control':
                                        assert move['overlap'] == 2*(2**bits)+len(TAIL)
                                    compressed_overlap.apply_cyclic_overlap(arena, roots, move)
                                status, reason = 'COMPLETE', None
                            except CompressedLimit as exc:
                                status, reason = 'LIMIT', str(exc)
                            measurements[arm] = dict(seconds=perf_counter()-start, status=status,
                                reason=reason, move=move, nodes=len(arena.rules)-1,
                                gain=before-sum(arena.lengths[r] for r in roots) if status == 'COMPLETE' else None,
                                stats=arena.stats.copy())
                    if repetition:
                        samples.append(dict(order=order, measurements=measurements))
                operations.append(dict(family=family, bits=bits, samples=samples))
                print(family, bits, {a:(measurements[a]['status'],
                    median(s['measurements'][a]['seconds'] for s in samples)) for a in arms}, flush=True)
        diagram, original, prefix, initial_alive, words = residual()
        for repetition in range(args.rounds+1):
            order, measurements = arms[:], {}
            rng.shuffle(order)
            for arm in order:
                with environment(arm) as helper:
                    start = perf_counter()
                    arena = WordArena(max_work=20000000)
                    roots = [arena.reduce(arena.from_word(word)) for word in words]
                    alive, moves = set(initial_alive), deepcopy(prefix)
                    move = helper(arena, roots)
                    assert move is not None
                    compressed_overlap.apply_cyclic_overlap(arena, roots, move)
                    moves.append(move)
                    assert compressed_search._search(arena, roots, alive, moves, relator_moves=True)
                    elapsed = perf_counter()-start
                certificate = dict(original, moves=moves, version=_certificate_version(moves),
                                   remaining_generator=next(iter(alive)))
                replays = {}
                for compressed in (False, True):
                    replay_start = perf_counter()
                    assert verify_group_certificate(diagram, certificate,
                        compressed=compressed, max_work=20000000)
                    replays['compressed' if compressed else 'literal'] = perf_counter()-replay_start
                measurements[arm] = dict(seconds=elapsed, status='COMPLETE', first_move=move,
                    moves=len(moves), nodes=len(arena.rules)-1, stats=arena.stats.copy(),
                    replay_seconds=replays, certificate=certificate)
            if repetition:
                residuals.append(dict(order=order, measurements=measurements))
        print('gordian-residual', {a:median(s['measurements'][a]['seconds'] for s in residuals)
              for a in arms}, flush=True)
    result = dict(python=sys.version, platform=platform.platform(), baseline_commit=BASELINE,
        seed=3110, measured_rounds=args.rounds, excluded_warmups=1,
        kernel_max_work=2000000, query_max_work=20000000, max_nodes=100000,
        policy='Historical global-LCS default retained; witness_first is an explicit optional helper',
        query_scope='Fresh PD, full recognition and independent replay; digests checked outside timing',
        operation_scope='Grammar construction, unsuccessful whole-donor check, cyclic partial query and checked application',
        residual_scope='Fresh compression of real reachable Gordian residual, witness move and search continuation; existing prefix recovery excluded',
        replay_scope='Complete reconstructed original-PD certificate; each backend measured independently outside residual timer',
        gain_warning='Threshold-plus-maximal-extension can select smaller gain at a different alignment; gain-tradeoff records an explicit instance',
        censoring='LIMIT is incomplete search, not a negative result or completed-time denominator',
        rows=rows, operations=operations, residual_samples=residuals)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
