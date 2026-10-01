#!/usr/bin/env python3
"""Canonical scalar history bounds replace per-cell range assumptions.

The duration/height geometry and selector/selected-source relations remain
explicit external hypotheses. No arbitrary-duration compiler is claimed.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import group_four_register_history as prior


PARAMETERS = ['x', 'q', 'P', 'history_bound']
PARAMETERS += [f'H{i}' for i in range(4)]
PARAMETERS += [f'{tag}{i}{sign}' for i in range(4)
               for tag in ('S', 'Z') for sign in ('p', 'm')]


def source():
    c = prior.Circuit()
    prior.aggregate(c, 1, 1, 1, 4, 1, [1]*4, [1]*8, [1]*8)
    schedule = [(name, op, 8 if name == 'B' else left, right)
                for name, op, left, right in c.schedule]
    schedule += [('history_sum01', '+', 'H0', 'H1'),
                 ('history_sum012', '+', 'history_sum01', 'H2'),
                 ('history_sum', '+', 'history_sum012', 'H3'),
                 ('history_bounded', '+', 'history_sum', 'history_bound')]
    pairs = [(f'left{i}', f'right{i}') for i in range(4)]
    pairs.append(('history_bounded', 'P'))
    return schedule, pairs


def execute(values):
    env = dict(values)
    for name, op, left, right in source()[0]:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env, tuple(env[a]-env[b] for a, b in source()[1])


def source_checks():
    schedule, pairs = source()
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in schedule)
    assert counts == {'M': 15, 'A': 32} and len(schedule) == 47
    available = set(PARAMETERS+['alpha', 'beta'])
    for name, op, left, right in schedule:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    rng, negative_endpoints = random.Random(4701532), 0
    for _ in range(512):
        values = {name: rng.randrange(1, 25) for name in PARAMETERS}
        values.update(alpha=24, beta=12)
        env, residuals = execute(values)
        q, P = values['q'], values['P']
        D, r = q*q, 24*values['x']+12
        B = 8*D
        initials = [D+q, D+1]*2
        finals = [D+q+r*q+1, D+1-r*(r*q+1)]*2
        expected = []
        for i in range(4):
            delta = values[f'Z{i}p']-values[f'Z{i}m']-D*(values[f'S{i}p']-values[f'S{i}m'])
            H = values[f'H{i}']
            expected.append(B*(H+delta)-H-finals[i]*P+initials[i])
        expected.append(sum(values[f'H{i}'] for i in range(4))+values['history_bound']-P)
        assert residuals == tuple(expected) and env['B'] == B
        negative_endpoints += finals[1] < 0
    return dict(operations=47, multiplications=15, additions_subtractions=32,
                equations=5, positive_history_fields=21, external_geometry=['q', 'P'],
                source=schedule, comparisons=pairs, full_residual_identities=512,
                negative_computed_terminal_fixtures=negative_endpoints)


def canonical_digits(number, base, duration):
    assert 0 <= number < base**duration
    digits = []
    for _ in range(duration):
        number, digit = divmod(number, base)
        digits.append(digit)
    assert number == 0
    return digits


def fixture(word, q, histories, x=1, alpha=1, beta=1):
    B, t = 8*q*q, len(word)
    P = B**t
    digits = [canonical_digits(H, B, t) for H in histories]
    states = [tuple(digits[i][j] for i in range(4)) for j in range(t)]
    rebuilt, selectors, selected = prior.fields(word, states, B)
    assert rebuilt == histories and all(H > 0 for H in histories)
    bound = P-sum(histories)
    assert bound > 0
    values = dict(x=x, alpha=alpha, beta=beta, q=q, P=P, history_bound=bound)
    values.update({f'H{i}': histories[i] for i in range(4)})
    for i in range(4):
        for index, sign in enumerate(('p', 'm')):
            values[f'S{i}{sign}'] = selectors[2*i+index]
            values[f'Z{i}{sign}'] = selected[2*i+index]
    env, residuals = execute(values)
    actual = [tuple(q*q+v for v in state) for state in prior.vector_trace(word, q)]
    expected_end = (env['U'], env['V'])*2
    exact = states == actual[:-1] and actual[-1] == expected_end
    assert all(r == 0 for r in residuals) == exact
    return env, residuals, states, actual


def history_checks():
    rng = random.Random(478)
    words = height_cases = 0
    for t in range(2, 5):
        for word in product(range(9), repeat=t):
            q = 2**t + (3 if words % 2 else 0)
            B, P = 8*q*q, (8*q*q)**t
            actual = [tuple(q*q+v for v in state) for state in prior.vector_trace(word, q)]
            assert all(0 < value < 2*q*q for state in actual for value in state)
            H, _, _ = prior.fields(word, actual[:-1], B)
            assert sum(H) < P
            env, residuals, _, _ = fixture(word, q, H)
            assert residuals[:4] == tuple((actual[-1][i]-(env['U'] if i%2 == 0 else env['V']))*P for i in range(4))
            words += 1
            height_cases += len(actual)
    arbitrary = zero_digits = high_digits = 0
    for _ in range(1536):
        t = rng.randrange(2, 9)
        q = 2**t+rng.randrange(8)
        B, P = 8*q*q, (8*q*q)**t
        word = tuple(rng.randrange(9) for _ in range(t))
        H = [rng.randrange(1, P//5) for _ in range(4)]
        if arbitrary < 16:
            H = [1, 1, 1, 1]
        _, residuals, states, _ = fixture(word, q, H)
        zero_digits += sum(v == 0 for state in states for v in state)
        high_digits += sum(v >= B//4 for state in states for v in state)
        assert any(residuals)
        arbitrary += 1
    accepted = mutations = largest_bits = 0
    for alpha, beta, x in [(1, 1, x) for x in range(1, 7)]+[(24, 12, 1)]:
        r = alpha*x+beta
        raw = prior.target_word(r)
        for padding in (0, 2):
            word = raw+(0,)*padding
            t, q = len(word), 2**len(word)
            B, P = 8*q*q, (8*q*q)**t
            states = [tuple(q*q+v for v in state) for state in prior.vector_trace(word, q)]
            H, _, _ = prior.fields(word, states[:-1], B)
            assert sum(H) < P
            assert not any(fixture(word, q, H, x, alpha, beta)[1])
            accepted += 1
            largest_bits = max(largest_bits, P.bit_length())
            for i in range(4):
                for position in (0, t//2, t-1):
                    bad = list(H)
                    bad[i] += B**position
                    assert sum(bad) < P
                    assert any(fixture(word, q, bad, x, alpha, beta)[1])
                    mutations += 1
    return dict(exhaustive_physical_words=words, genuine_state_rows=height_cases,
                arbitrary_canonical_histories=arbitrary, supplied_zero_digits=zero_digits,
                supplied_digits_at_or_above_quarter_radix=high_digits,
                actual_target_traces=accepted, rebuilt_selection_mutations_rejected=mutations,
                largest_length_power_bits=largest_bits,
                scope='No per-digit history positivity or half-radix bound is assumed in the converse.')


def verify():
    return dict(status='PASS_FOUR_REGISTER_CANONICAL_HISTORY47',
                arithmetic=source_checks(), histories=history_checks(),
                hypotheses='t>=2, q>=2^t, B=8q^2, P=B^t; one-hot-or-idle selectors and exact digitwise selections.',
                remaining='Duration/height geometry, physical selector typing, selected-source products and regular macro control are not included in47.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
