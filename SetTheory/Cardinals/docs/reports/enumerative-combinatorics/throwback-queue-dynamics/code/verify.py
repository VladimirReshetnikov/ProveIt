"""Reproduce exhaustive checks and CSV/JSON artifacts (standard library only)."""
from __future__ import annotations
import argparse
import csv
import json
import math
import random
import time
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path
from throwback import (first_obstruction, finite_orbit, sorted_statistics,
                       critical, admissible, bounded_step, bounded_inverse,
                       finite_horizon)


def verify_finite(max_n: int) -> list[dict]:
    output = []
    for n in range(2, max_n + 1):
        count = cores = max_period = max_transient = 0
        observed_critical_profiles = set()
        for weights in product(range(1, n), repeat=n):
            count += 1
            certificate = first_obstruction(weights)
            assert certificate is not None and certificate.verify()
            transient, states, leaders = finite_orbit(weights)
            cycle_leaders = leaders[transient:]
            recurrent = set(cycle_leaders)
            assert recurrent == set(certificate.core_labels), (weights, certificate, recurrent)
            assert set(leaders) == set(range(certificate.first_bad_index + 1))
            first_order = list(dict.fromkeys(leaders))
            assert first_order == list(range(certificate.first_bad_index + 1))
            assert critical(certificate.core_weights)
            stats = sorted_statistics(certificate.core_weights, closed=True)
            observed_period = len(cycle_leaders)
            assert observed_period == stats['period']
            labeled = sorted(recurrent, key=lambda i: (weights[i], i))
            counter = Counter(cycle_leaders)
            assert tuple(Fraction(counter[i], observed_period) for i in labeled) == stats['frequencies']
            # Every position outside the recurrent prefix is constant on the cycle.
            r = len(recurrent)
            assert all(set(s[:r]) == recurrent for s in states[transient:])
            assert all(s[r:] == states[transient][r:] for s in states[transient:])
            max_period = max(max_period, observed_period)
            max_transient = max(max_transient, transient)
            if recurrent == set(range(n)):
                cores += 1
                observed_critical_profiles.add(tuple(sorted(weights)))
            assert (recurrent == set(range(n))) == critical(weights)
        assert cores == (n - 1) ** (n - 1)
        assert len(observed_critical_profiles) == math.comb(2 * (n - 1), n - 1) // n
        output.append(dict(n=n, words=count, critical_words=cores,
                           critical_multisets=len(observed_critical_profiles),
                           max_period=max_period, max_transient=max_transient))
    return output


def all_bounded_states(weights: tuple[int, ...]):
    for state in product(*(range(x + 1) for x in weights)):
        if len(set(state)) == len(state):
            yield state


def verify_bounded(max_value: int, max_r: int) -> list[dict]:
    records = []
    for r in range(1, max_r + 1):
        profiles = total_states = total_cycles = perfect_profiles = 0
        max_period = 0
        for weights in combinations_with_replacement(range(1, max_value + 1), r):
            if not admissible(weights):
                continue
            profiles += 1
            stats = sorted_statistics(weights)
            states = set(all_bounded_states(weights))
            assert len(states) == stats['configurations']
            total_states += len(states)
            for state in states:
                nxt = bounded_step(weights, state)
                assert nxt in states
                assert bounded_inverse(weights, nxt) == state
                assert bounded_step(weights, bounded_inverse(weights, state)) == state
            cycles = 0
            unseen = set(states)
            while unseen:
                start = next(iter(unseen))
                state = start
                cycle = []
                while state in unseen:
                    unseen.remove(state)
                    cycle.append(state)
                    state = bounded_step(weights, state)
                assert state == start
                assert len(cycle) == stats['period'], (weights, len(cycle), stats)
                counts = Counter(s.index(0) if 0 in s else -1 for s in cycle)
                for i, freq in enumerate(stats['frequencies']):
                    assert Fraction(counts[i], len(cycle)) == freq
                assert Fraction(counts[-1], len(cycle)) == stats['remaining']
                cycles += 1
            assert cycles == stats['cycles']
            total_cycles += cycles
            perfect_profiles += cycles == 1
            max_period = max(max_period, stats['period'])
        records.append(dict(r=r, max_value=max_value, profiles=profiles,
                            states=total_states, cycles=total_cycles,
                            perfect_profiles=perfect_profiles, max_period=max_period))
    return records


def verify_wait_or_trap(max_n: int) -> int:
    # Independent dynamic check of the universal 2^p-1 waiting-or-barrier bound.
    trials = 0
    for n in range(2, max_n + 1):
        for weights in product(range(1, n), repeat=n):
            transient, states, leaders = finite_orbit(weights)
            period = len(states) - transient
            for p in range(n):
                deadline = 2 ** p - 1
                found = False
                for t in range(deadline + 1):
                    k = t if t < len(states) else transient + (t - transient) % period
                    state = states[k]
                    if state[0] == p:
                        found = True
                        break
                    if any(p not in state[:r] and max(weights[i] for i in state[:r]) < r
                           for r in range(1, p + 1)):
                        found = True
                        break
                assert found, (weights, p, deadline)
                trials += 1
    return trials


def verify_sparse_and_horizon(seed: int = 20260919) -> dict:
    rng = random.Random(seed)
    random_cases = 0
    for _ in range(1500):
        length = rng.randrange(2, 101)
        weights = [rng.randrange(1, length + 1) if rng.random() < .85
                   else 10 ** 40 + rng.randrange(100) for _ in range(length)]
        cert = first_obstruction(weights)
        naive = None
        for j in range(length):
            if not admissible(weights[:j + 1]):
                naive = j
                break
        assert (None if cert is None else cert.first_bad_index) == naive
        if cert is not None:
            assert cert.verify()
        random_cases += 1
    # Exact finite-horizon projection, compared with a genuinely closed,
    # much longer finite queue whose tail is guaranteed not to matter yet.
    horizon_cases = 0
    for _ in range(200):
        steps = 20
        window = 5
        long_weights = [rng.randrange(1, 60) for _ in range(80)]
        leaders, visible = finite_horizon(long_weights[:steps + window], steps, window)
        queue = list(range(len(long_weights)))
        reference = []
        for __ in range(steps):
            h = queue.pop(0)
            reference.append(h)
            queue.insert(long_weights[h], h)
        assert leaders == reference and visible == tuple(queue[:window])
        horizon_cases += 1
    return dict(seed=seed, sparse_cases=random_cases, horizon_cases=horizon_cases)


def write_csv(path: Path, records: list[dict]) -> None:
    with path.open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=records[0].keys())
        writer.writeheader()
        writer.writerows(records)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=7)
    parser.add_argument('--max-value', type=int, default=7)
    parser.add_argument('--max-r', type=int, default=5)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    start = time.perf_counter()
    finite = verify_finite(args.max_n)
    print('finite checks complete', finite, flush=True)
    bounded = verify_bounded(args.max_value, args.max_r)
    print('bounded checks complete', bounded, flush=True)
    waiting_trials = verify_wait_or_trap(5)
    random = verify_sparse_and_horizon()
    report = dict(status='all assertions passed', finite_queue=finite,
                  bounded_configurations=bounded, waiting_bound_trials=waiting_trials,
                  random_checks=random, elapsed_seconds=round(time.perf_counter() - start, 3))
    args.output.mkdir(parents=True, exist_ok=True)
    write_csv(args.output / 'finite_queue_checks.csv', finite)
    write_csv(args.output / 'bounded_configuration_checks.csv', bounded)
    (args.output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
