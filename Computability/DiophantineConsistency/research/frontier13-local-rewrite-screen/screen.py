#!/usr/bin/env python3
"""Deterministic finite-field rejection certificate for a bounded DAG search.

The filter never promotes a sampled match to a polynomial identity. For the
declared syntactic family, a true identity must match on all sampled tuples.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

if not __debug__:
    raise RuntimeError('this certificate requires Python assertions enabled')

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
INPUTS = (
    ('adaptive-square-sums/candidate.json', '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828', 87),
    ('adaptive-direct-ordinate86/candidate.json', 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f', 86),
)
MODULUS = 2305843009213693951
SEED = 773845
LITERALS = (0, 1, 2, 3, 4)
SAMPLES = 3


def op(operator, left, right):
    if operator == '+':
        return tuple((a + b) % MODULUS for a, b in zip(left, right))
    if operator == '-':
        return tuple((a - b) % MODULUS for a, b in zip(left, right))
    if operator == '*':
        return tuple(a * b % MODULUS for a, b in zip(left, right))
    raise ValueError(operator)


def living_count(rows, output, replacements):
    table = {row[0]: row for row in rows}
    for row in replacements:
        table[row[0]] = row
    seen, todo = set(), [output]
    while todo:
        node = todo.pop()
        if not isinstance(node, str) or node in seen:
            continue
        seen.add(node)
        if node in table:
            todo.extend(table[node][2:])
    return len(set(table) & seen)


def scan(graph):
    rows = graph['source']
    output = graph['output']
    variables = graph['witnesses'] + graph['fixed_numerals']
    assert len(variables) == len(set(variables))
    assert 'SCREEN_TEMP' not in variables and all(r[0] != 'SCREEN_TEMP' for r in rows)
    assert len({r[0] for r in rows}) == len(rows)
    assert living_count(rows, output, []) == len(rows)
    rng = random.Random(SEED)
    values = {name: tuple(rng.randrange(2, MODULUS - 1) for _ in range(SAMPLES))
              for name in variables}
    for literal in LITERALS:
        values[str(literal)] = (literal,) * SAMPLES
    available = list(values)
    pairs = {}
    counts = Counter()
    inverse_cache = {}

    def add_operations(new, previous):
        for earlier in previous + [new]:
            # + and * are commutative; include both subtraction orders.
            for kind, left, right in (('+', earlier, new), ('*', earlier, new),
                                      ('-', earlier, new), ('-', new, earlier)):
                signature = op(kind, values[left], values[right])
                pairs.setdefault(signature, []).append((kind, left, right))

    for i, name in enumerate(available):
        add_operations(name, available[:i])

    for index, (target, kind, left, right) in enumerate(rows):
        assert kind in ('+', '-', '*') and target not in values
        assert str(left) in values and str(right) in values
        wanted = op(kind, values[str(left)], values[str(right)])
        # Literal zero is already in the earlier-node list. Nonzero targets
        # make multiplication by the literal zero an impossible match.
        assert wanted != values['0'], ('zero target sample', target)

        # A direct alias costs no gate; report all sample matches rather than
        # treating them as proven equalities. There are none in these graphs.
        for earlier in available:
            if values[earlier] == wanted:
                counts['alias_sample_matches'] += 1

        # Replace this target by one binary operation on earlier nodes.
        for first in pairs.get(wanted, ()):
            counts['one_gate_sample_matches'] += 1
            replacement = [target, first[0], first[1], first[2]]
            if living_count(rows, output, [replacement]) < len(rows):
                counts['one_gate_strict_candidates'] += 1

        # Two gates: t = a op b, then target = t op z or z - t. Both
        # operands of the first gate and z are earlier nodes/literals.
        for z in available:
            zv = values[z]
            alternatives = [('+', op('-', wanted, zv), False),
                            ('-', op('+', wanted, zv), False),
                            ('-', op('-', zv, wanted), True)]
            if z == '0':
                assert all(v == 0 for v in zv)
            else:
                # Fail closed rather than silently excluding any zero or
                # non-invertible divisor signature from the product search.
                assert all(v != 0 for v in zv), ('zero divisor sample', target, z)
                if zv not in inverse_cache:
                    inverse_cache[zv] = tuple(pow(v, -1, MODULUS) for v in zv)
                alternatives.append(('*', op('*', wanted, inverse_cache[zv]), False))
            for final, needed, reverse in alternatives:
                for first in pairs.get(needed, ()):
                    counts['two_gate_sample_matches'] += 1
                    a, b = (z, 'SCREEN_TEMP') if reverse else ('SCREEN_TEMP', z)
                    replacements = [['SCREEN_TEMP', first[0], first[1], first[2]],
                                    [target, final, a, b]]
                    if living_count(rows, output, replacements) < len(rows):
                        counts['two_gate_strict_candidates'] += 1

        # Also enumerate both final operands equal to t. A subtraction t-t
        # is zero and was excluded by the checked nonzero target sample.
        for signature, expressions in pairs.items():
            for final in ('+', '*'):
                if op(final, signature, signature) != wanted:
                    continue
                for first in expressions:
                    counts['self_gate_sample_matches'] += 1
                    replacements = [['SCREEN_TEMP', first[0], first[1], first[2]],
                                    [target, final, 'SCREEN_TEMP', 'SCREEN_TEMP']]
                    if living_count(rows, output, replacements) < len(rows):
                        counts['self_gate_strict_candidates'] += 1

        values[target] = wanted
        add_operations(target, available)
        available.append(target)
    return {key: counts[key] for key in (
        'alias_sample_matches', 'one_gate_sample_matches', 'one_gate_strict_candidates',
        'two_gate_sample_matches', 'two_gate_strict_candidates',
        'self_gate_sample_matches', 'self_gate_strict_candidates')}


def main():
    results = []
    for name, pin, size in INPUTS:
        raw = (RESEARCH / name).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == pin
        graph = json.loads(raw)
        assert len(graph['source']) == size and len(graph['witnesses']) == 13
        result = scan(graph)
        assert result['alias_sample_matches'] == 0
        assert result['one_gate_strict_candidates'] == 0
        assert result['two_gate_strict_candidates'] == 0
        assert result['self_gate_strict_candidates'] == 0
        results.append({'graph': name, 'sha256': pin, 'rows': size, **result})

    # Positive control: (x+y)z-xz=yz. Replacing d or out drops live gates.
    toy = {'witnesses': ['x', 'y', 'z', 'w'], 'fixed_numerals': [],
           'source': [['a', '+', 'x', 'y'], ['b', '*', 'a', 'z'],
                      ['c', '*', 'x', 'z'], ['d', '-', 'b', 'c'],
                      ['out', '*', 'd', 'w']], 'output': 'out'}
    toy_result = scan(toy)
    assert toy_result['one_gate_strict_candidates'] > 0
    assert toy_result['two_gate_strict_candidates'] > 0
    # A second positive control requires considering t*t at the final gate.
    self_toy = {'witnesses': ['x', 'y', 'z', 'w'], 'fixed_numerals': [],
                'source': [['a', '+', 'x', 'y'], ['b', '+', 'a', 'z'],
                           ['c', '*', 'b', 'b'], ['d', '+', 'c', 'w'],
                           ['out', '-', 'd', 'w']], 'output': 'out'}
    self_result = scan(self_toy)
    assert self_result['self_gate_strict_candidates'] > 0
    print(json.dumps({'status': 'PASS_BOUNDED_REJECTION_CERTIFICATE',
                      'modulus': MODULUS, 'seed': SEED, 'samples': SAMPLES,
                      'literal_set': list(LITERALS), 'graphs': results,
                      'positive_control': toy_result,
                      'self_gate_positive_control': self_result}, sort_keys=True))


if __name__ == '__main__':
    main()
