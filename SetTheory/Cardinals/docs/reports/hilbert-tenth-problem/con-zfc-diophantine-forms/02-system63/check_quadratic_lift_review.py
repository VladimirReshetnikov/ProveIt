#!/usr/bin/env python3
"""Independent exact reconstruction of the advertised natural-variable lift.

This reviewer does not import quadratic_lift.py. Its dense exponent-vector
representation is separate from the producer's named sparse monomials.
The coefficient ports remain formal symbols; degree counts only unknowns.
"""
import argparse
import hashlib
import json
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=Path(__file__).with_name('fixed_input63_ordinary_system.json'))
    parser.add_argument('--lift', type=Path, default=Path(__file__).with_name('quadratic_lift.json'))
    parser.add_argument('--producer', type=Path, default=Path(__file__).with_name('quadratic_lift.py'))
    parser.add_argument('--proof', type=Path, default=Path(__file__).with_name('QUADRATIC_LIFT.md'))
    parser.add_argument('--receipt', type=Path,
                        default=Path(__file__).with_name('quadratic_lift_review_checks.json'))
    args = parser.parse_args()
    source_raw = args.source.read_bytes()
    packet_raw = args.lift.read_bytes()
    source = json.loads(source_raw)
    packet = json.loads(packet_raw)
    source_hash = hashlib.sha256(source_raw).hexdigest()
    require(source_hash == 'fae15df15460d41868db8fbc96e4d7619004e9ac04b390dcc44379a8e9ff1bfb',
            'source differs from the mathematically reviewed ordinary system')
    require(packet['source_sha256'] == source_hash, 'lift source hash mismatch')
    witnesses = source['witnesses']
    constants = source['fixed_numerals']
    original = source['source']
    changed = []
    for name, op, left, right in original:
        if name == 'aux_square_gap':
            require((op, left, right) == ('-', 'H2', 'aux_y2'), 'changed original gap')
            op, left, right = '-', 'aux_y2', 'H2'
        elif name == 'norm_aux':
            require((op, left, right) == ('+', 'L17', 'aux_y2'), 'changed original norm')
            op, left, right = '-', 'aux_y2', 'L17'
        changed.append([name, op, left, right])
    require(packet['nonnegative_gate_source'] == changed, 'unexpected sign-adjusted circuit')
    variables = ['v_' + w for w in witnesses] + ['g_' + row[0] for row in changed]
    require(len(witnesses) == 16 and len(changed) == 63 and len(variables) == 79,
            'wrong source or lifted size')
    require(packet['variables'] == variables, 'variable list mismatch')
    require(packet['fixed_numerals'] == constants, 'coefficient list mismatch')
    names = constants + variables
    require(len(names) == len(set(names)) == 84, 'duplicate polynomial names')
    lookup = {name: j for j, name in enumerate(names)}
    zero = (0,) * len(names)

    def scalar(n):
        return {zero: n} if n else {}

    def atom(name):
        powers = [0] * len(names)
        powers[lookup[name]] = 1
        return {tuple(powers): 1}

    def linear(left, right, multiplier=1):
        result = dict(left)
        for powers, coefficient in right.items():
            result[powers] = result.get(powers, 0) + multiplier * coefficient
            if result[powers] == 0:
                del result[powers]
        return result

    def times(left, right):
        result = {}
        for powers, coefficient in left.items():
            for other, factor in right.items():
                product = tuple(x + y for x, y in zip(powers, other))
                result[product] = result.get(product, 0) + coefficient * factor
        return {powers: coefficient for powers, coefficient in result.items() if coefficient}

    def decode(terms):
        result = {}
        for term in terms:
            coefficient = term['coefficient']
            require(type(coefficient) is int and coefficient != 0, 'invalid sparse coefficient')
            powers = [0] * len(names)
            for name, exponent in term['powers'].items():
                require(name in lookup and type(exponent) is int and exponent > 0,
                        'invalid sparse monomial')
                powers[lookup[name]] = exponent
            powers = tuple(powers)
            require(powers not in result, 'duplicate sparse monomial')
            result[powers] = coefficient
        return result

    env = {x: linear(scalar(1), atom('v_' + x)) for x in witnesses}
    env.update({c: atom(c) for c in constants})
    expected = []
    for name, op, left, right in changed:
        require(name not in env, 'duplicate gate output')
        require(op in ('+', '-', '*'), 'unknown source operation')
        l = scalar(left) if type(left) is int else env[left]
        r = scalar(right) if type(right) is int else env[right]
        rhs = times(l, r) if op == '*' else linear(l, r, -1 if op == '-' else 1)
        output = atom('g_' + name)
        expected.append((name, linear(output, rhs, -1)))
        env[name] = output
    for j, (left, right) in enumerate(source['comparisons'], 1):
        l = scalar(left) if type(left) is int else env[left]
        r = scalar(right) if type(right) is int else env[right]
        expected.append(('comparison_' + str(j), linear(l, r, -1)))
    require(len(expected) == len(packet['equations']) == 70, 'equation count mismatch')
    for (name, polynomial), supplied in zip(expected, packet['equations']):
        require(name == supplied['name'], 'equation order mismatch')
        require(polynomial == decode(supplied['polynomial']), 'residual coefficient mismatch: ' + name)
    quartic = {}
    for _, polynomial in expected:
        quartic = linear(quartic, times(polynomial, polynomial))
    require(quartic == decode(packet['quartic']), 'quartic coefficient mismatch')
    degree = lambda p: max(sum(powers[len(constants):]) for powers in p)
    require(max(degree(p) for _, p in expected) == 2, 'quadratic degree mismatch')
    require(degree(quartic) == 4, 'quartic degree mismatch')
    require(len(quartic) == packet['quartic_terms'] == 286, 'formal term count mismatch')
    leader = [0] * len(names)
    leader[lookup['v_tau_root']] = 4
    require(quartic.get(tuple(leader)) == 1, 'missing coefficient-independent quartic monomial')
    occurring = {names[j] for p in quartic for j, e in enumerate(p) if e and j >= len(constants)}
    require(occurring == set(variables), 'an advertised unknown does not occur')
    audited_subtractions = {
        'norm_first', 'norm_main', 'q_minus_F', 'q_minus_FZ', 'C_after_alpha',
        'index_difference', 'Lm1', 'norm_index', 'norm_transport',
        'auxiliary_Tf_minus_one', 'aux_u_rhs', 'aux_square_gap',
        'f2_minus_one', 'norm_aux',
    }
    actual_subtractions = {row[0] for row in changed if row[1] == '-'}
    require(actual_subtractions == audited_subtractions, 'subtraction proof coverage mismatch')
    for _, _, left, right in changed:
        for operand in (left, right):
            if type(operand) is int:
                require(operand >= 0, 'unreviewed negative source literal')
    receipt = {
        'status': 'PASS',
        'review_method': 'Independent exponent-vector reconstruction; no producer import',
        'positive_source_unknowns': 16,
        'nonnegative_lifted_unknowns': 79,
        'gate_equations': 63,
        'final_comparisons': 7,
        'exact_residuals_compared': 70,
        'maximum_residual_degree': 2,
        'expanded_quartic_formal_terms_compared': 286,
        'exact_quartic_degree': 4,
        'v_tau_root_power_4_coefficient': 1,
        'all_79_unknowns_occur': True,
        'subtractions_covered_by_mathematical_positivity_audit': 14,
        'source_sha256': source_hash,
        'lift_sha256': hashlib.sha256(packet_raw).hexdigest(),
        'producer_sha256': hashlib.sha256(args.producer.read_bytes()).hexdigest(),
        'proof_note_sha256': hashlib.sha256(args.proof.read_bytes()).hexdigest(),
        'scope': 'Natural-variable equivalence uses the accompanying zero-set positivity proof; no K215 solution or kernel proof claimed',
    }
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
