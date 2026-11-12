"""Independent finite test of affine-depth generated-equation zero instances.

This is a falsification aid, not a proof of soundness or bi-interpretability.
The number decoder is semantic and separate from the opening implementation.
"""
import itertools
import json
import random
from pathlib import Path


class Budget(Exception):
    pass


def opening(a, image=None, depth=0, floor=-2, fuel=120):
    if fuel <= 0:
        raise Budget
    if type(a) is list:
        return [opening(b, image, depth + len(a) + 1, floor, fuel - 1)
                for b in a]
    if floor <= a < depth:
        return a
    return opening(image, depth=1, floor=floor, fuel=fuel-1) if depth % 2 else 0


def number(a, env, valuation, budget):
    budget[0] -= 1
    if budget[0] <= 0:
        raise Budget
    if type(a) is not list:
        n = int(a // 1)
        if n < 0:
            return valuation[n]
        return 0 if n == 0 else env[(n - 1) // 2]
    arity = len(a)
    if arity == 1:
        return 1 + number(a[0], (0,) + env, valuation, budget)
    if arity == 3:
        counter, seed, body = a
        n = number(counter, (0, 0) + env, valuation, budget)
        value = number(seed, (0, 0) + env, valuation, budget)
        if n > 14:
            raise Budget
        for _ in range(n):
            value = number(body, (value, value) + env, valuation, budget)
        return value
    # Zero, binary annotations, and all numerical arities >= 4 mean zero.
    return 0


def generate(predecessor, seed, body, flag):
    packet_term = [predecessor, seed, body]
    equation = [[flag and [predecessor], seed, body],
                opening(body, packet_term, 1) if flag else seed]
    return opening(equation, -3, floor=-3)


def main():
    rng = random.Random(2026111001)
    scalars = [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
               10, 11, 12, 13, 14, 15, 16, 0.5, 2.5, -1.5]
    small = scalars + [[], [0], [1], [2], [3], [4], [5], [6], [7],
                       [8], [9], [10], [-1], [0, 0], [1, 2],
                       [0, 0, 0, 0], [1, 2, 3, 4], [0] * 5, [1] * 6]

    def tree(depth):
        if depth == 0 or rng.random() < .5:
            return rng.choice(scalars)
        return [tree(depth-1) for _ in range(rng.randrange(7))]

    cases = itertools.chain(
        itertools.product(small, scalars, small),
        ((tree(3), tree(3), tree(3)) for _ in range(12000)))
    valuations = [{-3: 0, -2: x, -1: y}
                  for x in range(3) for y in range(3)]
    attempts = generated = evaluated = bounded = 0
    for predecessor, seed, body in cases:
        for flag in (0, 1):
            attempts += 1
            try:
                equation = generate(predecessor, seed, body, flag)
            except (TypeError, ValueError, IndexError, RecursionError, KeyError):
                continue
            except Budget:
                bounded += 1
                continue
            generated += 1
            for valuation in valuations:
                try:
                    # The affine Eq constructor adds one zero-valued slot.
                    left = number(equation[0], (0,), valuation, [12000])
                    right = number(equation[1], (0,), valuation, [12000])
                except Budget:
                    bounded += 1
                    continue
                if left != right:
                    result = {'result': 'COUNTEREXAMPLE',
                              'packet': [predecessor, seed, body, flag],
                              'equation': equation, 'valuation': valuation,
                              'left': left, 'right': right}
                    (Path(__file__).resolve().parents[1] / 'evidence' / 'independent_supply_result.json').write_text(
                        json.dumps(result, indent=2) + '\n')
                    print(json.dumps(result, indent=2))
                    raise SystemExit(1)
                evaluated += 1
    result = {'result': 'PASS_FINITE_ZERO_INSTANCE_AUDIT',
              'attempted_packets': attempts, 'generated_equations': generated,
              'evaluated_valuations': evaluated, 'budget_limited_cases': bounded,
              'seed': 2026111001,
              'scope': 'Constructed computation Supply at fresh w=0; extra Eq zero slot; numerical arities >=4 decode to zero. Not a universal proof.'}
    (Path(__file__).resolve().parents[1] / 'evidence' / 'independent_supply_result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
