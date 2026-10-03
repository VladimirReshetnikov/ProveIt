#!/usr/bin/env python3
"""Independent verifier of exported factored natural quadratic polynomials.

Does not import the generator. Usage:
  python code/check_certificate.py artifacts/countdown_certificate.json
Optional --game independently checks every trajectory and gap against the game.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path
from math import lcm


def check(path, game_path=None):
    data = json.loads(Path(path).read_text())
    if data.get('format') != 'natural-quadratic-certificate-v1':
        raise ValueError('unknown certificate format')
    labels, values = data['variable_labels'], data['assignment']
    if len(labels) != len(values) or len(set(labels)) != len(labels):
        raise ValueError('invalid variable labels')
    if any(type(v) is not int or v < 0 for v in values):
        raise ValueError('witness outside the natural numbers')
    total = 0
    for terms in data['squared_linear_forms']:
        if len(set(j for j, _ in terms)) != len(terms):
            raise ValueError('duplicate variable in linear form')
        s = 0
        for j, a in terms:
            if type(j) is not int or not -1 <= j < len(values) or type(a) is not int:
                raise ValueError('invalid linear form')
            s += a*(1 if j == -1 else values[j])
        total += s*s
    for u, v in data['nonnegative_products']:
        if not 0 <= u < len(values) or not 0 <= v < len(values):
            raise ValueError('invalid product')
        total += values[u]*values[v]
    meta = data['metadata']
    N, b, T = meta['states'], meta['binary_states'], meta['horizon']
    assert len(values) == (N+2*b)*T
    assert len(data['squared_linear_forms']) == (N+b)*T+meta.get('endpoint_squares',1)
    assert len(data['nonnegative_products']) == b*T
    if game_path:
        game = json.loads(Path(game_path).read_text())
        N = game['states']
        if 'initial_terminal_payoffs' in game:
            assert [Fraction(a,meta['initial_denominator']) for a in meta['input_numerators']] == [
                Fraction(v) for v in game['initial_terminal_payoffs']]
        eta = Fraction(game['common_uniform_reset'])
        delta = Fraction(game['discount'])
        reward = Fraction(game.get('common_reward','0'))
        rows = []
        for actions in game['base_actions']:
            ra = []
            for action in actions:
                r = [eta/N]*N
                for j, probability in action:
                    r[j] += (1-eta)*Fraction(probability)
                assert sum(r) == 1 and min(r) >= 0
                ra.append(r)
            rows.append(ra)
        D = lcm(*(p.denominator for ra in rows for r in ra for p in r))
        assert D == meta['probability_denominator']
        current = meta['initial_numerators']
        assignment = dict(zip(labels, values))
        for t in range(T):
            forcing = int(meta.get('witness_scale',1)*(delta.denominator*D)**(t+1)*reward)
            following = []
            for i, ra in enumerate(rows):
                av = [sum(int(D*p)*x for p, x in zip(r, current))*delta.numerator + forcing for r in ra]
                y = max(av) if game['owners'][i] == 'max' else min(av)
                assert assignment[f'X_{t+1}_{i}'] == y
                if len(av) == 2:
                    for a in range(2):
                        gap = y-av[a] if game['owners'][i] == 'max' else av[a]-y
                        assert assignment[f'gap_{t}_{i}_{a}'] == gap
                following.append(y)
            current = following
        r, s = meta['observed_pair']
        if meta.get('terminal_mode') == 'point':
            target = Fraction(meta['target'])*meta['witness_scale']*(delta.denominator*D)**T
            truth = all(x == target for x in current)
        elif meta.get('terminal_mode') == 'consensus':
            truth = len(set(current)) == 1
        else:
            truth = current[r] == current[s]
        assert (total == 0) == truth
    return {'polynomial_value': total, 'natural_witnesses': len(values),
            'squared_linear_forms': len(data['squared_linear_forms']),
            'complementarity_products': len(data['nonnegative_products']),
            'independent_game_check': bool(game_path)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate')
    parser.add_argument('--game')
    args = parser.parse_args()
    print(json.dumps(check(args.certificate, args.game), indent=2))
