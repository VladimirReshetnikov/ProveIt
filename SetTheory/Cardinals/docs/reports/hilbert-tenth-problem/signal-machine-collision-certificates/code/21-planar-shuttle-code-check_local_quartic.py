#!/usr/bin/env python3
"""Independent reader/checker of the actual exported expanded quartic.

Does not import the certificate generator. The sparse polynomial is rebuilt
from exported residuals and compared exactly, then evaluated independently.
All checks remain active under Python -O.
"""
from collections import Counter
from itertools import combinations_with_replacement
from math import prod
from pathlib import Path
from random import Random
import argparse
import json
import local_rule


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def evaluate(terms, values):
    return sum(t['coefficient']*prod(values[i] for i in t['variables']) for t in terms)


def run(path):
    certificate = json.loads(path.read_text())
    coordinates = [tuple(p) for p in certificate['input_coordinates']]
    gates = certificate['gates']
    residuals = certificate['residuals']
    polynomial = certificate['expanded_polynomial']
    num_ext = certificate['external_variable_count']
    require(num_ext == 79 and len(coordinates) == 78, 'Input count mismatch')
    require(len(gates) == 614 and len(residuals) == 693, 'Gate/residual count mismatch')
    require(len(certificate['variable_order']) == 693, 'Total variable count mismatch')
    # Re-expand using unordered term pairs, independently of generator's loops.
    rebuilt = Counter()
    for residual in residuals:
        for i, j in combinations_with_replacement(range(len(residual)), 2):
            a, b = residual[i], residual[j]
            monomial = tuple(sorted(a['variables'] + b['variables']))
            rebuilt[monomial] += a['coefficient']*b['coefficient']*(1 if i == j else 2)
    rebuilt = {m: c for m, c in rebuilt.items() if c}
    exported = {tuple(t['variables']): t['coefficient'] for t in polynomial}
    require(len(exported) == len(polynomial), 'Repeated collected monomial')
    require(rebuilt == exported, 'Expanded quartic disagrees with residual SOS')
    require(max(map(len, exported)) == 4, 'Quartic degree mismatch')
    rng = Random(456031)
    counts = Counter()

    def local_value(bits):
        support = {p for p, bit in zip(coordinates, bits) if bit}
        return local_rule.evaluate(local_rule.neighborhood(support, (0, 0)))

    def witness(bits, output):
        values = list(bits) + [output]
        for gate in gates:
            require(gate['target'] == len(values), 'Gate order or target mismatch')
            require(gate['previous'] < gate['target'] and gate['input'] < 78,
                    'Gate dependency is not acyclic')
            value = values[gate['input']]
            if gate['complement']:
                value = 1-value
            values.append(values[gate['previous']]*value)
        return values

    cases = [[0]*78, [1]*78]
    for _ in range(220):
        density = rng.choice((0.025, 0.08, 0.25, 0.5, 0.8))
        cases.append([int(rng.random() < density) for _ in range(78)])
    for indicator in certificate['indicators']:
        for _ in range(8):
            bits = [rng.randrange(2) for _ in range(78)]
            for i in indicator['ones']:
                bits[i] = 1
            for i in indicator['zeros']:
                bits[i] = 0
            cases.append(bits)
    for bits in cases:
        output = local_value(bits)
        values = witness(bits, output)
        require(all(v in (0, 1) for v in values), 'Natural witness is not binary')
        residual_values = [evaluate(r, values) for r in residuals]
        require(all(v == 0 for v in residual_values), 'Correct local output fails residuals')
        require(evaluate(polynomial, values) == 0, 'Correct local output fails quartic')
        values[78] = 1-output
        require(evaluate(polynomial, values) == 1, 'Wrong binary output not rejected')
        counts['binary_local_cases'] += 1

    # Perturb every auxiliary of a valid witness: one of its forced gates fails.
    values = witness([0]*78, 0)
    for index in range(num_ext, len(values)):
        values[index] += 1
        total = sum(evaluate(r, values)**2 for r in residuals)
        require(total > 0 and evaluate(polynomial, values) == total,
                'Perturbed auxiliary admitted or SOS mismatch')
        values[index] -= 1
        counts['auxiliary_perturbation_checks'] += 1
    for _ in range(60):
        values = [rng.randrange(-2, 4) for _ in range(693)]
        total = sum(evaluate(r, values)**2 for r in residuals)
        require(evaluate(polynomial, values) == total, 'Nonbinary SOS identity failure')
        counts['nonbinary_identity_checks'] += 1

    # Concrete essentiality witnesses, independent of top-degree reasoning.
    backgrounds = [[0]*78]
    for item in certificate['indicators']:
        bits = [0]*78
        for i in item['ones']:
            bits[i] = 1
        backgrounds.append(bits)
    essentiality = []
    for index, coordinate in enumerate(coordinates):
        found = False
        for base in backgrounds:
            bits = list(base)
            before = local_value(bits)
            bits[index] = 1-bits[index]
            after = local_value(bits)
            if before != after:
                essentiality.append({'coordinate': list(coordinate),
                                     'input_mask_78': str(sum(b << i for i, b in enumerate(base))),
                                     'before': before, 'after': after})
                found = True
                break
        require(found, ('No concrete essentiality witness', coordinate))
    return {
        'status': 'PASS', 'counts': certificate['counts'],
        'checks': dict(sorted(counts.items())),
        'exact_expanded_polynomial_terms': len(polynomial),
        'essential_input_cells': len(essentiality),
        'essentiality_witnesses': essentiality,
        'scope': certificate['scope'],
        'optimized_safe': True,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate', type=Path, default=Path('local-quartic-certificate.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.certificate)
    serialized = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(serialized)
    print(serialized, end='')
