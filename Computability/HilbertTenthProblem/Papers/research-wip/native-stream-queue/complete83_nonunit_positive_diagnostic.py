#!/usr/bin/env python3
"""Bounded full-source nonunit diagnostic; no compiler-admissibility claim."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'complete83_free_coefficient_scout.py': 'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
    'complete83_free_coefficient_scout.json': '682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
    'complete83_free_coefficient_scout.md': '867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
}
FACTORS = ['norm_first', 'norm_main', 'norm_input', 'norm_aux',
           'norm_index', 'norm_transport', 'norm_strong']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact_div(a, b):
    require(type(a) is int and type(b) is int and b != 0, 'division types')
    q, r = divmod(a, b)
    require(r == 0, 'nonintegral division')
    return q


def pell(A, n):
    require(type(A) is int and A >= 2 and type(n) is int and n >= 0, 'Pell input')
    disc = A*A - 1
    x, y, u, v = 1, 0, A, 1
    while n:
        if n & 1:
            x, y = x*u + disc*y*v, x*v + y*u
        u, v = u*u + disc*v*v, 2*u*v
        n //= 2
    require(x*x-disc*y*y == 1, 'Pell norm')
    return x, y


def same_typed(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same_typed(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same_typed(x, y) for x, y in zip(a, b))
    return a == b


def verify(root):
    root = Path(root).resolve()
    for name, digest in PINS.items():
        require(sha((root/name).read_bytes()) == digest, 'pin mismatch: '+name)
    packet = json.loads((root/'complete83_free_coefficient_scout.json').read_text())['packet']
    require(packet['factors'] == FACTORS, 'factor order')
    source = packet['source']
    require(len(source) == 83 and packet['output'] == 'polynomial', 'complete source')

    D, c = pell(26, 1351)
    tau, psi_first = pell(257, 855)
    k = 2*psi_first
    mu, kappa = pell(26, 17)
    gamma = exact_div(D-24*c-2, 99)
    rho = exact_div(mu-24*kappa+4, 99)
    eta, zeta = c-8*k, 9*k-c
    require(8*k < c < 9*k, 'strict main/first ratio')
    require(gamma > rho > 0, 'positive supplied rho and sigma')
    values = dict(
        Jrep=1, F=1, alpha=1, transport_quotient=670, f=1,
        h=exact_div(k-2702, 16), aux_coefficient_root=26,
        auxiliary_quotient=1, s=1, w=1, tau_root=tau,
        eta=eta, zeta=zeta, y_aux=2703, Z=1,
        delta=exact_div(kappa-17, 675), rho=rho, sigma=gamma-rho,
        x=1, Bm1=1, Kconstant=1, twice_cell_bits=2,
        inner_bits=15, MC=2694, MF=2,
    )
    require(set(values) == set(packet['free']), 'exact free interface')
    require(len(packet['witnesses']) == 18 and len(packet['fixed_numerals']) == 6,
            'declared interface counts')
    require(set(packet['witnesses']) | set(packet['fixed_numerals']) | {'x'} == set(values),
            'complete supplied coordinate partition')
    require(all(type(v) is int and v > 0 for v in values.values()), 'positive supplied values')
    assignment = dict(values)
    dependencies = {}
    M = A = 0
    for row in source:
        require(type(row) is list and len(row) == 4, 'row format')
        name, op, left, right = row
        require(type(name) is str and name not in values and op in ('+', '-', '*'), 'fresh row')
        for port in (left, right):
            require(type(port) is int or type(port) is str and port in values, 'closed row')
        x = values[left] if type(left) is str else left
        y = values[right] if type(right) is str else right
        values[name] = x+y if op == '+' else x-y if op == '-' else x*y
        dependencies[name] = [z for z in (left, right) if type(z) is str]
        M += op == '*'
        A += op != '*'
    live, stack = set(), [packet['output']]
    while stack:
        port = stack.pop()
        if port not in live:
            live.add(port)
            stack.extend(dependencies.get(port, []))
    require(live == set(values), 'all paid gates and supplied ports live')
    require((M, A) == (46, 37), 'actual paid ledger')
    require([values[name] for name in FACTORS] == [1, 1, 1, 1, 1, -675, -1],
            'actual nonunit factor values')
    require(values['A'] == 675 and values['polynomial'] == 0, 'complete output zero')
    require(values['r_lhs'] == 2701 and values['aux_u_rhs'] == -2701, 'actual auxiliary argument')
    require(values['R10a'] == c and values['R14'] == D, 'actual main ports')
    require(values['index_rhs'] == kappa and values['exponent_rhs'] == mu, 'actual input ports')
    require(values['W'] == -4 and values['marked_rhs'] == -3, 'actual signed computed ports')
    require(all(values['A'] % values[name] == 0 for name in FACTORS), 'integer divisor consequence')
    require(values['q'] == 2 and assignment['MC'] >= assignment['Bm1'], 'invalid compiler slice')
    mf0 = assignment['MF'] - assignment['Bm1']
    require(mf0 == 1 and mf0 % 8 != 4, 'mask exclusion')
    require(assignment['inner_bits'] > assignment['twice_cell_bits']//2, 'width exclusion')
    require(assignment['Kconstant']//2 == 0, 'program numeral exclusion')

    return {
        'schema': 'complete83-nonunit-positive-diagnostic-v1',
        'checker_sha256': sha(Path(__file__).read_bytes()),
        'parent_pins': dict(PINS),
        'scope': {
            'full_polynomial_zero_materialized': True,
            'all_supplied_witnesses_positive': True,
            'all_fixed_numerals_positive': True,
            'valid_fixed_compiler_slice': False,
            'false_accepted_input_claim': False,
            'universal_bound_claim': False,
            'diagnostic_only': True,
        },
        'pell_parameters': {'main_A': 26, 'main_index': 1351, 'first_P': 257,
                            'first_index': 855, 'input_index': 17},
        'source': source,
        'output': packet['output'],
        'free': packet['free'],
        'witnesses': packet['witnesses'],
        'fixed_numerals': packet['fixed_numerals'],
        'positive_assignment_hex': {name: hex(assignment[name]) for name in packet['free']},
        'actual_register_values_hex': {row[0]: hex(values[row[0]]) for row in source},
        'factor_names': FACTORS,
        'factor_values': [values[name] for name in FACTORS],
        'Delta': values['A'],
        'full_output': values['polynomial'],
        'actual_ledger': {'M': M, 'A': A, 'total': M+A},
        'supplied_counts': {'witnesses': 18, 'ordinary_inputs': 1, 'fixed_numerals': 6},
        'ratio_checks': {'8k_less_c': 8*k<c, 'c_less_9k': c<9*k, 'gamma_greater_rho': gamma>rho},
        'diagnostic_computed_ports': {'q': values['q'], 'a': values['R12'], 'Pell_A': values['R12']+2,
                                     'packed_R': values['r_lhs'], 'V': values['aux_u_rhs'],
                                     'W': values['W'], 'C': values['marked_rhs'], 'MF0': mf0},
        'compiler_exclusions': {
            'B': 2, 'q_below_16': True, 'MC_outside_mask_range': True,
            'MF0_wrong_mod8_and_range': True, 'inner_bits_exceeds_cell_bits': True,
            'K_div_B_is_zero': True, 'N_equals_one_fails_2x_less_N': True,
        },
        'maximum_free_bit_length': max(v.bit_length() for v in assignment.values()),
        'maximum_computed_bit_length': max(abs(values[row[0]]).bit_length() for row in source),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = verify(args.root)
    serialized = json.dumps(result, indent=2, sort_keys=True)+'\n'
    require(same_typed(result, json.loads(serialized)), 'typed JSON roundtrip')
    if args.expect:
        require(same_typed(result, json.loads(args.expect.read_text())), 'saved receipt mismatch')
    else:
        args.output.write_text(serialized)
    print('PASS: all 83 literal gates; 25 positive supplied values; factors 1,1,1,1,1,-675,-1; output 0; NONCOMPILER')


if __name__ == '__main__':
    main()
