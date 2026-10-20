#!/usr/bin/env python3
"""Bounded positive-macro deletion of every strict single-entry checkpoint.

Only the unique incoming action changes. The old hidden state is excluded from
the boundary relation, which is exact state/head/tape equality elsewhere.
Survivors remain hypotheses until an independent boundary verifier accepts.
"""
from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import itertools
import json
import sys
import time
import search_v3 as shared

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def old_goals(old, hidden, entry, word, radius, fuel):
    """Positive old endpoints only; no read or write outside the window."""
    q, h, m = entry[0], 0, word
    goals = {}
    halt = None
    for tick in range(1, fuel + 1):
        if q == 254 or not -radius <= h <= radius:
            break
        bit = (m >> (h + radius)) & 1
        w, d, q = old[q, bit]
        m = (m & ~(1 << (h + radius))) | (w << (h + radius))
        h += d
        if q == 254:
            halt = tick
        if q != hidden:
            goals.setdefault((q, h, m), tick)
    return goals, halt


def check_entry(old, new, hidden, entry, patterns, cache, radius, fuel, deadline):
    histogram = collections.Counter()
    for word in patterns:
        if time.monotonic() >= deadline:
            return {'status': 'INCOMPLETE_TIME_LIMIT'}
        if word not in cache:
            cache[word] = old_goals(old, hidden, entry, word, radius, fuel)
        goals, oldhalt = cache[word]
        q, h, m = entry[0], 0, word
        seen = set()
        joined = None
        reason = 'fuel_exhausted'
        for tick in range(1, fuel + 1):
            if q == 254 or not -radius <= h <= radius:
                reason = 'new_exits_window'
                break
            if (q, h, m) in seen:
                reason = 'new_repeats'
                break
            seen.add((q, h, m))
            bit = (m >> (h + radius)) & 1
            w, d, q = new[q, bit]
            m = (m & ~(1 << (h + radius))) | (w << (h + radius))
            h += d
            if q == 254:
                if oldhalt is not None:
                    joined = oldhalt, tick
                else:
                    reason = 'new_halt_without_old_halt'
                break
            n = goals.get((q, h, m))
            if n is not None:
                joined = n, tick
                break
        if joined is None:
            return {'status': 'BOUNDARY_FILTER_REJECTED', 'window': word,
                    'reason': reason, 'radius': radius, 'fuel': fuel}
        histogram[joined] += 1
    return {'status': 'BOUNDARY_MACRO_FILTER_SURVIVOR', 'contexts': len(patterns),
            'histogram': [[a, b, n] for (a, b), n in sorted(histogram.items())],
            'scope': 'Author filter only; independent verifier required.'}


def controls():
    # A two-step hidden detour plus a return joins the new one-step action.
    old = {(1, 0): (0, 1, 2), (1, 1): (1, 1, 4)}
    for b in (0, 1):
        old[2, b] = b, 1, 3
        old[3, b] = b, -1, 4
        old[4, b] = b, 1, 4
    new = {row: action for row, action in old.items() if row[0] != 2}
    new[1, 0] = 0, 1, 4
    radius = 2
    patterns = [m for m in range(1 << (2 * radius + 1)) if not (m >> radius) & 1]
    cache = {}
    good = check_entry(old, new, 2, (1, 0), patterns, cache, radius, 9, float('inf'))
    assert good['status'] == 'BOUNDARY_MACRO_FILTER_SURVIVOR'
    assert good['histogram'] == [[3, 1, len(patterns)]]
    new[1, 0] = 0, 1, 254
    bad = check_entry(old, new, 2, (1, 0), patterns, cache, radius, 9, float('inf'))
    assert bad['status'] == 'BOUNDARY_FILTER_REJECTED'
    assert bad['reason'] == 'new_halt_without_old_halt'
    return {'status': 'TWO_SYNTHETIC_CONTROLS_PASS', 'positive': good,
            'invalid_early_halt': bad, 'shared_old_goal_cache': True,
            'scope': 'These finite examples only; no independent verifier invocation.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=120)
    args = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        ap.error('Assertions must be enabled')
    if not 0 < args.seconds <= 120:
        ap.error('The time bound can only be narrowed')
    args.output.mkdir(parents=True, exist_ok=False)
    inputs = json.loads((ROOT / 'inputs.json').read_text())
    descriptors = inputs['seeds'] + [inputs['universal_checker'], inputs['decoder_allocation']]
    pins = {str((ROOT / d['path']).resolve()): d['sha256'] for d in descriptors}
    assert all(sha(Path(p)) == h for p, h in pins.items())
    checker_path = (ROOT / inputs['universal_checker']['path']).resolve()
    checker = shared.load_checker(checker_path)
    decoder = set(map(int, json.loads((ROOT / inputs['decoder_allocation']['path']).read_text())))
    for name, path in [('search_hidden_states.py', Path(__file__)),
                       ('search_v3.py', ROOT / 'search_v3.py'),
                       ('check_joint_fold.py', checker_path), ('inputs.json', ROOT / 'inputs.json')]:
        (args.output / name).write_bytes(path.read_bytes())
    dump(args.output / 'controls.json', controls())
    started = time.monotonic()
    deadline = started + args.seconds
    radius, fuel = 7, 97
    seeds, tables = [], {}
    for seed in inputs['seeds']:
        old, start = checker.read((ROOT / seed['path']).resolve())
        states = sorted({q for q, b in old})
        assert len(old) == 438 and len(states) == 219 and 254 not in states
        incoming = collections.defaultdict(list)
        for row, action in old.items():
            incoming[action[2]].append(row)
        eligible, excluded = [], []
        for q in states:
            rows = incoming[q]
            if q == start or len(rows) != 1 or rows[0][0] == q:
                excluded.append({'state': q, 'incoming_rows': [list(x) for x in rows],
                                 'reason': 'initial' if q == start else
                                 ('incoming_count' if len(rows) != 1 else 'self_entry')})
            else:
                eligible.append({'hidden': q, 'entry': list(rows[0]),
                                 'allocation_class': 'decoder' if q in decoder else 'engine_or_helper',
                                 'status': 'NOT_STARTED', 'candidate_count': 876,
                                 'attempted': 0, 'completed': 0, 'rejected': 0, 'survivors': 0})
        assert len(eligible) + len(excluded) == 219
        seeds.append({'seed': seed['name'], 'states': eligible, 'excluded': excluded,
                      'eligible_count': len(eligible), 'candidate_count': 876 * len(eligible)})
        tables[seed['name']] = old, start
    hits = []
    attempted = completed = 0
    stop = None
    with gzip.open(args.output / 'rejections.jsonl.gz', 'wt') as rejected:
        for seed in seeds:
            if time.monotonic() >= deadline:
                stop = 'TIME_LIMIT'
                break
            old, start = tables[seed['seed']]
            invariant = checker.domain(old, start, radius)
            for stats in seed['states']:
                if time.monotonic() >= deadline:
                    stop = 'TIME_LIMIT'
                    break
                hidden, entry = stats['hidden'], tuple(stats['entry'])
                patterns = sorted(m for m in invariant[entry[0]] if (m >> radius) & 1 == entry[1])
                if len(patterns) > 2:
                    patterns = [patterns[0], patterns[-1], *patterns[1:-1]]
                stats['entry_contexts'] = len(patterns)
                stats['status'] = 'RUNNING'
                new = {row: action for row, action in old.items() if row[0] != hidden}
                targets = sorted({q for q, b in new} | {254})
                assert len(targets) == 219 and hidden not in targets
                # This structural gate applies to the whole family, not sampled paths.
                assert [row for row, action in new.items() if action[2] == hidden] == [entry]
                cache = {}
                for action in itertools.product((0, 1), (-1, 1), targets):
                    if time.monotonic() >= deadline:
                        stop = 'TIME_LIMIT'
                        break
                    new[entry] = action
                    attempted += 1
                    stats['attempted'] += 1
                    result = check_entry(old, new, hidden, entry, patterns, cache, radius, fuel, deadline)
                    if result['status'] == 'INCOMPLETE_TIME_LIMIT':
                        stats['unfinished_action'] = list(action)
                        stop = 'TIME_LIMIT'
                        break
                    completed += 1
                    stats['completed'] += 1
                    if result['status'] == 'BOUNDARY_FILTER_REJECTED':
                        stats['rejected'] += 1
                        rejected.write(json.dumps({'id': attempted, 'seed': seed['seed'],
                            'hidden': hidden, 'entry': list(entry), 'action': list(action),
                            'failure': result}, separators=(',', ':')) + '\n')
                    else:
                        assert all(z != hidden for w, d, z in new.values())
                        assert all(new[row] == value for row, value in old.items()
                                   if row[0] != hidden and row != entry)
                        directory = args.output / f'survivor-{attempted:06d}'
                        directory.mkdir()
                        native = directory / 'candidate.native.tm'
                        native.write_bytes(shared.encode(new, start))
                        dump(directory / 'filter.json', result)
                        hits.append({'id': attempted, 'seed': seed['seed'], 'hidden': hidden,
                            'entry': list(entry), 'action': list(action), 'filter': str(directory / 'filter.json'),
                            'candidate_sha256': sha(native)})
                        stats['survivors'] += 1
                stats['cached_old_windows'] = len(cache)
                stats['status'] = 'COMPLETE' if stats['completed'] == 876 else 'INCOMPLETE_TIME_LIMIT'
                if stop:
                    break
            if stop:
                break
    assert all(sha(Path(p)) == h for p, h in pins.items())
    out = {'status': 'COMPLETE_SINGLE_ENTRY_SEARCH' if stop is None else 'INCOMPLETE_' + stop,
           'seconds': time.monotonic() - started, 'wall_limit': args.seconds,
           'source_sha256': sha(Path(__file__)), 'shared_source_sha256': sha(ROOT / 'search_v3.py'),
           'inputs': pins, 'seeds': seeds, 'attempted': attempted, 'completed': completed,
           'candidate_count': sum(s['candidate_count'] for s in seeds), 'hits': hits,
           'radius': radius, 'fuel': fuel, 'rejection_stream_sha256': sha(args.output / 'rejections.jsonl.gz'),
           'family': 'Every noninitial state with exactly one incoming row, counting self-loops; require its predecessor distinct. Delete it and vary only that row over both writes, directions, all remaining states and halt.',
           'boundary_relation': 'Exact state/head/tape equality outside the hidden state. Positive old/new blocks at the unique changed entry, or both halt. No relation imposed at hidden state.',
           'scope': 'Author bounded filter only. No independent verifier invoked; survivors require separate verification. Failures are not semantic counterexamples or a lower bound.'}
    dump(args.output / 'result.json', out)
    print(json.dumps({k: v for k, v in out.items() if k not in ('seeds', 'inputs')}, indent=2))


if __name__ == '__main__':
    main()
