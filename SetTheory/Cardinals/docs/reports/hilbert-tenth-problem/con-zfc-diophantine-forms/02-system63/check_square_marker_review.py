#!/usr/bin/env python3
"""Independent replay of the final 72/74-gate square-marker sources."""
import argparse
import hashlib
import json
from pathlib import Path
import random


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(rows, supplied):
    env = dict(supplied)
    for name, op, left, right in rows:
        require(name not in env, 'duplicate output')
        l = left if type(left) is int else env[left]
        r = right if type(right) is int else env[right]
        require(op in ('+', '-', '*'), 'invalid operation')
        env[name] = l + r if op == '+' else l - r if op == '-' else l * r
    return env


def diagonal(rows, witnesses, constants):
    def trim(value):
        while len(value) > 1 and not value[-1]:
            value.pop()
        return value

    def add(left, right, sign=1):
        result = [0] * max(len(left), len(right))
        for j, n in enumerate(left):
            result[j] += n
        for j, n in enumerate(right):
            result[j] += sign * n
        return trim(result)

    def multiply(left, right):
        result = [0] * (len(left) + len(right) - 1)
        for j, a in enumerate(left):
            for k, b in enumerate(right):
                result[j + k] += a * b
        return trim(result)

    env = {name: [0, 1] for name in witnesses}
    env.update({name: [value] for name, value in constants.items()})
    for name, op, left, right in rows:
        l = [left] if type(left) is int else env[left]
        r = [right] if type(right) is int else env[right]
        env[name] = multiply(l, r) if op == '*' else add(l, r, -1 if op == '-' else 1)
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--receipt', type=Path,
                        default=Path(__file__).with_name('square_marker_review_checks.json'))
    args = parser.parse_args()
    cases = [
        ('fixed_input73.json', 'fixed_input72_square_marker.json',
         '4d405f6377b8a6d8fd094919342db912d5626bb8c229dd933b7cee4874c90d40', 72, 157),
        ('fixed_input75_ordinary.json', 'fixed_input74_ordinary_square_marker.json',
         'af930c639b29b0a62937f696ec0d777560119bc5baee0503e6d1378c6cb50718', 74, 101),
    ]
    records = []
    rng = random.Random(720074215)
    factor_names = ['norm_first', 'norm_main', 'norm_aux', 'norm_index',
                    'norm_transport', 'norm_strong', 'seven_units']
    for parent_name, child_name, pinned_parent, total, expected_degree in cases:
        parent_raw = (args.sources / parent_name).read_bytes()
        child_raw = (args.sources / child_name).read_bytes()
        parent = json.loads(parent_raw)
        child = json.loads(child_raw)
        require(hashlib.sha256(parent_raw).hexdigest() == pinned_parent,
                'parent differs from independently reviewed source')
        for field in ('witnesses', 'fixed_numerals', 'witness_domain', 'snapshot'):
            require(parent[field] == child[field], 'changed source interface: ' + field)
        expected = []
        for row in parent['source']:
            if row[0] == 'marker_unit':
                require(row == ['marker_unit', '+', 'marker_square', 1], 'unexpected old marker')
                continue
            expected.append(['all_with_marker', '*', 'seven_units', 'marker_square']
                            if row[0] == 'all_with_marker' else row)
        require(child['source'] == expected, 'more than the specified marker change')
        rows = child['source']
        multiplication = sum(row[1] == '*' for row in rows)
        require(len(rows) == total and multiplication == 41, 'wrong literal operation ledger')
        require(child['operations'] == {'multiplication': 41,
                'addition_subtraction': total - 41, 'total': total}, 'wrong recorded ledger')
        dependencies = {name: {name} for name in child['witnesses'] + child['fixed_numerals']}
        graph = {}
        for name, op, left, right in rows:
            require(name not in dependencies, 'repeated register')
            operands = [x for x in (left, right) if type(x) is not int]
            dependencies[name] = set().union(*(dependencies[x] for x in operands))
            graph[name] = operands
        for name in factor_names:
            require('alpha' not in dependencies[name], 'alpha reaches a retained factor')
        live = {'polynomial'}
        pending = ['polynomial']
        while pending:
            for operand in graph.get(pending.pop(), []):
                if operand not in live:
                    live.add(operand)
                    pending.append(operand)
        require(set(graph).issubset(live), 'dead gate in final source')
        require(set(child['witnesses'] + child['fixed_numerals']).issubset(live), 'dead input')
        for _ in range(64):
            supplied = {name: rng.randrange(-4, 8)
                        for name in child['witnesses'] + child['fixed_numerals']}
            old = run(parent['source'], supplied)
            new = run(rows, supplied)
            shifted = run(rows, dict(supplied, alpha=supplied['alpha'] + 1))
            require(old['polynomial'] - new['polynomial'] == old['seven_units'],
                    'same-input polynomial identity failed')
            require(shifted['polynomial'] == old['polynomial']
                    - 2 * old['seven_units'] * old['marker_difference'],
                    'shifted polynomial identity failed')
            for factor in factor_names:
                require(old[factor] == new[factor] == shifted[factor], 'retained factor changed')
        constants = dict(Bm1=15, Kconstant=11, MC=2, MF=19, W0=8192)
        old_diagonal = diagonal(parent['source'], parent['witnesses'], constants)
        new_diagonal = diagonal(rows, child['witnesses'], constants)
        require(len(old_diagonal['polynomial']) - 1 == expected_degree, 'parent diagonal degree')
        require(len(new_diagonal['polynomial']) - 1 == expected_degree, 'child diagonal degree')
        require(old_diagonal['polynomial'][-1] == new_diagonal['polynomial'][-1],
                'top diagonal coefficient changed')
        require(len(new_diagonal['seven_units']) - 1 == expected_degree - 2,
                'removed marker summand has incorrect degree')
        records.append({
            'source': child_name,
            'sha256': hashlib.sha256(child_raw).hexdigest(),
            'reviewed_parent_sha256': pinned_parent,
            'positive_unknowns': len(child['witnesses']),
            'fixed_numerals': len(child['fixed_numerals']),
            'multiplications': multiplication,
            'additions_subtractions': total - multiplication,
            'total_gates': total,
            'exact_degree': expected_degree,
            'all_gates_and_inputs_live': True,
            'all_retained_factors_independent_of_alpha': True,
            'independent_signed_identity_fixtures': 64,
            'exact_univariate_replay': True,
            'multivariate_degree_argument': 'Same leading homogeneous form as reviewed parent; removed summand has degree two less',
        })
    proof_path = args.sources / 'SQUARED_MARKER_PROOF.md'
    receipt = {
        'status': 'PASS',
        'variants': records,
        'proof_note_sha256': hashlib.sha256(proof_path.read_bytes()).hexdigest() if proof_path.exists() else None,
        'diagnostic_coefficients_are_valid_compiler_slice': False,
        'scope': 'Independent literal replay plus mathematical marker-slack review; no positive K215 solution or kernel proof claimed',
        'seven_equation_system_and_quadratic_lift_modified': False,
    }
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
