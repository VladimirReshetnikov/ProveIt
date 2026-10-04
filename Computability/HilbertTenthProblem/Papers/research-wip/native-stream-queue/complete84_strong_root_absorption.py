#!/usr/bin/env python3
"""Fresh source identities for strong-root absorption; predecessors are inert."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
    'complete84_exterior_auxiliary_absorption.py': '46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9',
    'complete84_exterior_auxiliary_absorption.json': 'ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b',
    'complete84_exterior_auxiliary_absorption.md': '69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de',
    'complete84_signed_quotient_absorption.py': 'cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f',
    'complete84_signed_quotient_absorption.json': 'c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00',
    'complete84_signed_quotient_absorption.md': '79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9',
}
AUX = {'i', 'f', 'auxiliary_quotient', 'y_aux'}
FACTORS = ['norm_first', 'norm_main', 'norm_input', 'norm_index', 'norm_transport']
CUTS = ['A', 'R10a', 'r_lhs'] + FACTORS


def check(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            check(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def reject(value):
        raise ValueError('noninteger JSON ' + value)
    return json.loads(path.read_text(), object_pairs_hook=pairs,
                      parse_float=reject, parse_constant=reject)


def constant(n):
    return {(): n} if n else {}


def var(name):
    return {(name,): 1}


def add(a, b, sign=1):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, 0) + sign * coefficient
    return {m: c for m, c in result.items() if c}


def multiply(a, b):
    result = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m + n))
            result[key] = result.get(key, 0) + c * d
    return {m: c for m, c in result.items() if c}


def product(*values):
    result = constant(1)
    for value in values:
        result = multiply(result, value)
    return result


def power(value, n):
    return product(*[value for _ in range(n)])


def record(value):
    return [[list(m), c] for m, c in sorted(value.items())]


def symbolic_source(packet):
    rows = packet['source']
    dependencies = {name: {name} for name in packet['free']}
    known = set(dependencies)
    definitions = {}
    for row in rows:
        check(type(row) is list and len(row) == 4, 'binary source row')
        name, op, a, b = row
        check(type(name) is str and name not in known and op in ['+', '-', '*'], 'SSA/opcode')
        check(all(type(v) is int or type(v) is str and v in known for v in [a, b]), 'source topology')
        dependencies[name] = set().union(*(dependencies[v] for v in [a, b] if type(v) is str))
        known.add(name)
        definitions[name] = row
    outside = [row[0] for row in rows if not dependencies[row[0]] & AUX]
    supplied = [name for name in packet['free'] if name not in AUX]
    check(len(outside) == 64 and len(supplied) == 21, 'full85 exterior census')
    check(set(CUTS) <= set(outside), 'actual auxiliary-independent cuts')
    check([r for r in rows if 'f' in r[2:]] == [
        ['L16', '*', 'f', 'f'],
        ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']], 'sole two f consumers')
    check([r for r in rows if 'auxiliary_quotient' in r[2:]] == [
        ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']], 'sole quotient consumer')
    for row in [
        ['R12', '+', 'UM', 'sn2'], ['UM', '*', 'wn2', 'sn2'],
        ['a_square', '*', 'R12', 'R12'], ['a4', '*', 4, 'R12'],
        ['a4m5', '+', 'a4', 3], ['A', '+', 'a_square', 'a4m5']]:
        check(definitions[row[0]] == row, 'positive discriminant boundary')
    expanded = set()
    def run(f_value, quotient_value):
        memo = {name: var(name) for name in packet['free'] + CUTS}
        memo['f'], memo['auxiliary_quotient'] = f_value, quotient_value
        def at(name):
            if type(name) is int:
                return constant(name)
            if name not in memo:
                _, op, a, b = definitions[name]
                a, b = at(a), at(b)
                memo[name] = multiply(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
                expanded.add(name)
            return memo[name]
        return at(packet['output'])
    D, c, R, i, f, T, y = [var(n) for n in ['A', 'R10a', 'r_lhs', 'i', 'f', 'auxiliary_quotient', 'y_aux']]
    P5 = product(*(var(n) for n in FACTORS))
    Q = power(product(D, i, c, c), 2)
    V = add(product(c, add(product(T, f), constant(1), -1)), product(R, f, f), -1)
    Na = add(product(Q, add(power(V, 2), power(y, 2), -1)), power(y, 2))
    Ns = add(product(D, f, f), Q, -1)
    expected = add(product(P5, Na, Ns), D, -1)
    full = run(f, T)
    check(full == expected, 'full actual-source polynomial factor identity')
    check(run(product(constant(-1), f), product(constant(-1), T)) == full,
          'full simultaneous sign reversal')
    at_zero = run({}, T)
    zero_na = add(product(Q, add(power(c, 2), power(y, 2), -1)), power(y, 2))
    zero_formula = product(constant(-1), D,
        add(product(D, i, i, c, c, c, c, P5, zero_na), constant(1)))
    check(at_zero == zero_formula, 'full zero-f contraction')
    check(all('auxiliary_quotient' not in m for m in at_zero), 'quotient disappears at zero root')
    return dict(computed_exterior=outside, supplied_exterior=supplied,
        exact_cut_names=CUTS, expanded_output_ancestors=[r for r in rows if r[0] in expanded],
        full_coefficients=record(full), zero_f_coefficients=record(at_zero),
        full_sign_identity=True, full_zero_root_identity=True)


def chi_polynomials(last):
    A = var('A')
    result = [constant(1), A]
    for _ in range(2, last + 1):
        result.append(add(product(constant(2), A, result[-1]), result[-2], -1))
    return result


def compose(poly, inner):
    result = {}
    for monomial, coeff in poly.items():
        check(all(v == 'A' for v in monomial), 'univariate composition')
        result = add(result, product(constant(coeff), power(inner, len(monomial))))
    return result


def corroboration():
    polys = chi_polynomials(36)
    identities = []
    for r in range(1, 7):
        for s in range(1, 7):
            value = compose(polys[s], polys[r])
            check(value == polys[r*s], 'formal Pell chi composition')
            identities.append([r, s, len(value)])
    growth = []
    for D in range(2, 10):
        previous, current = 1, D
        for n in range(2, 17):
            previous, current = current, 2*D*current-previous
            check(current > D**n, 'strict chi power growth')
            growth.append([D, n])
    thresholds = []
    for t in range(9):
        for L in [1, 2, 3, 4, 7, 8, 9, 16, 17, 255, 256, 257]:
            bound = 4*t+(L-1).bit_length()
            for c in [max(2, bound), max(2, bound)+1]:
                check(c**c >= L*c**(4*t), 'integer cutoff endpoint')
            thresholds.append([t, L, bound])
    return dict(formal_composition_identities=identities, strict_growth_cases=growth,
        cutoff_cases=thresholds, scope='Finite polynomial/inequality corroboration only; no full native zeros')


def build(root, signed_root):
    for name, expected in PINS.items():
        path = (signed_root if name.startswith('complete84_signed_quotient_absorption.') else root) / name
        check(len(expected) == 64 and sha(path.read_bytes()) == expected, 'dependency pin ' + name)
    signed = read(signed_root / 'complete84_signed_quotient_absorption.json')
    check(signed['source_sha256'] == PINS['complete84_signed_quotient_absorption.py'], 'signed helper binding')
    packet = read(root / 'complete84_scaled_strong_output.json')['packet']
    check(len(packet['source']) == 84 and len(packet['free']) == 25, 'complete84 interface')
    check(signed['authenticated_parent_source'] == packet['source'], 'signed lemma binds the same complete source')
    check(signed['theorem']['normalized_rank'] == 'c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R', 'signed normalized-rank scope')
    check(signed['theorem']['old85_bound'] == 'absolute values <c^4' and not signed['theorem']['positive_T_parent_restoration_used'], 'direct signed exterior bound')
    identities = symbolic_source(packet)
    check(identities['computed_exterior'] == signed['census']['old_computed'] and identities['supplied_exterior'] == signed['census']['old_free'], 'same85 values in the signed-domain lemma')
    old = read(root / 'complete84_exterior_auxiliary_absorption.json')
    check(identities['computed_exterior'] == old['source_census']['computed_exterior_in_source_order'], 'actual old85 computed boundary')
    census = old['source_census']
    check(set(identities['supplied_exterior']) == set(census['exterior_witnesses'] + census['fixed_numerals'] + [census['ordinary_input']]), 'actual old85 supplied boundary')
    return dict(status='PASS_STRONG_ROOT_ABSORPTION', source_sha256=sha(Path(__file__).read_bytes()),
        pins=PINS, authenticated_source=packet['source'], source_evidence=identities,
        corroboration=corroboration(), theorem=dict(domain='Literal f=G in the old85 auxiliary-independent values',
            zero_G_sector='empty before native recovery', nonzero_map='f=abs(G), T=sign(G)*T',
            inherited_domain='positive f and arbitrary integer auxiliary quotient', strong_growth='f>c^c',
            cutoff='2d*x+b<R<c<4*degree(G)+ceil(log2 L)', whole_input_projection='finite'),
        scope=dict(predecessor_execution=False, new_circuit=False, generic_G_compiler=False,
            no_global_minimum_claim=True, no_positive_T_parent_map_claim=True))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--signed-root', type=Path)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root, args.signed_root or args.root)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    else:
        check(canonical(result) == canonical(read(args.expect)), 'exact typed receipt')
    print(result['status'], '64+21 boundary; full sign/zero-root identities')


if __name__ == '__main__':
    main()
