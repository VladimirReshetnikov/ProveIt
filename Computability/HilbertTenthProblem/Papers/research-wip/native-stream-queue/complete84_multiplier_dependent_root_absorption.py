#!/usr/bin/env python3
"""Fresh source evidence for multiplier-dependent root absorption; predecessors stay inert."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
    'complete84_strong_root_absorption.py': '3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c',
    'complete84_strong_root_absorption.json': '424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a',
    'complete84_strong_root_absorption.md': 'b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2',
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


def extended_interface(packet, old):
    removed = {'f', 'auxiliary_quotient', 'y_aux'}
    dependencies = {name: {name} for name in packet['free']}
    rows = packet['source']
    definitions = {r[0]: r for r in rows}
    for name, op, a, b in rows:
        dependencies[name] = set().union(*(dependencies[v] for v in [a, b] if type(v) is str))
    computed = [r[0] for r in rows if not dependencies[r[0]] & removed]
    supplied = [n for n in packet['free'] if n not in removed]
    check(len(computed) == 66 and len(supplied) == 22, 'exact88 literal boundary')
    check(set(computed) - set(old['computed_exterior']) == {'aux_coefficient_root', 'R16'}, 'only two added computed values')
    check(set(supplied) - set(old['supplied_exterior']) == {'i'}, 'only one added supplied value')
    for row in [
        ['c2', '*', 'R10a', 'R10a'], ['Ac2', '*', 'A', 'c2'],
        ['aux_coefficient_root', '*', 'i', 'Ac2'],
        ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
        ['scaled_f_square', '*', 'A', 'L16'],
        ['norm_strong', '-', 'scaled_f_square', 'R16']]:
        check(definitions[row[0]] == row, 'literal multiplier/strong boundary')
    old_names = old['computed_exterior'] + old['supplied_exterior']
    memo = {n: var(n) for n in old_names}
    memo['i'] = var('z')
    # Re-expand the real c² and Delta*c² producers rather than leave them as
    # independent coefficient ports: this proves the coefficient weights used.
    memo['c2'] = power(var('R10a'), 2)
    memo['Ac2'] = product(var('A'), memo['c2'])
    def at(n):
        if type(n) is int:
            return constant(n)
        if n not in memo:
            _, op, a, b = definitions[n]
            a, b = at(a), at(b)
            memo[n] = multiply(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
        return memo[n]
    S = at('aux_coefficient_root')
    Q = at('R16')
    check(S == product(var('A'), power(var('R10a'), 2), var('z')), 'actual S specialization')
    check(Q == product(power(var('A'), 2), power(var('R10a'), 4), power(var('z'), 2)), 'actual S² specialization')
    weights = [{ 'name': n, 'coefficient_c_exponent': 4, 'z_degree': 0 } for n in old_names]
    weights += [dict(name='i', coefficient_c_exponent=0, z_degree=1),
                dict(name='aux_coefficient_root', coefficient_c_exponent=3, z_degree=1),
                dict(name='R16', coefficient_c_exponent=6, z_degree=2)]
    check({x['name'] for x in weights} == set(computed + supplied) and len(weights) == 88, 'one weight for every actual argument')
    check(all(not dependencies[n] & removed for n in computed + supplied), 'sign map fixes all88 arguments')
    return dict(computed=computed, supplied=supplied,
        excluded_computed=[r[0] for r in rows if r[0] not in computed],
        added_computed=[definitions[n] for n in ['aux_coefficient_root', 'R16']],
        multiplier_polynomials=dict(S=record(S), S_squared=record(Q)),
        pointwise_argument_weights=weights)


def pell_polynomials(last):
    A = var('a0')
    chi = [constant(1), A]
    psi = [{}, constant(1)]
    for _ in range(2, last + 1):
        chi.append(add(product(constant(2), A, chi[-1]), chi[-2], -1))
        psi.append(add(product(constant(2), A, psi[-1]), psi[-2], -1))
    return chi, psi


def compose(poly, inner):
    result = {}
    for monomial, coefficient in poly.items():
        check(set(monomial) <= {'a0'}, 'univariate Pell polynomial')
        result = add(result, product(constant(coefficient), power(inner, len(monomial))))
    return result


def integer_pell(A, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = A*x+(A*A-1)*y, x+A*y
    return x, y


def corroboration():
    chi, psi = pell_polynomials(36)
    compositions = []
    for r in range(1, 7):
        for s in range(1, 7):
            value = product(psi[r], compose(psi[s], chi[r]))
            check(value == psi[r*s], 'formal normalized psi composition')
            compositions.append([r, s, len(value)])
    growth = []
    for D in range(2, 10):
        for n in range(2, 17):
            _, value = integer_pell(D, n)
            check(value >= n*D**(n-1), 'positive first odd-binomial term')
            growth.append([D, n, value])
    monomials = []
    for de in range(9):
        for di in range(9-de):
            for ds in range(9-de-di):
                for dq in range(9-de-di-ds):
                    t = de+di+ds+dq
                    coefficient_weight = 4*de+3*ds+6*dq
                    z_degree = di+ds+2*dq
                    check(coefficient_weight <= 6*t and z_degree <= 2*t, 'weighted monomial bound')
                    monomials.append([de, di, ds, dq, coefficient_weight, z_degree])
    thresholds = []
    for t in range(9):
        for L in [1, 2, 3, 4, 7, 8, 9, 16, 17, 255, 256, 257]:
            K = L*L+2
            b = max(12*t, 5)
            cutoff = b+1+(K-1).bit_length()
            for c in [cutoff, cutoff+1]:
                check(L*L*c**(12*t)+c**5+2 <= K*c**b, 'coefficient norm upper bound')
                check(c**(c-1) >= K*c**b, 'strict integer exclusion endpoint')
            thresholds.append([t, L, b, K, cutoff])
    # Small main/strong Pell components exercise the integer root estimate.
    # They do not satisfy the full compiled source and are not native zeros.
    components = []
    for A0 in range(2, 5):
        for R in range(2, 5):
            D, c = integer_pell(A0, R)
            f, psi_m = integer_pell(A0, R*c)
            check(psi_m % (c*c) == 0, 'component normalized strong divisibility')
            i = psi_m // (c*c)
            Delta = A0*A0-1
            check(f*f-Delta*c**4*i*i == 1 and i > c**(c-1), 'component strong growth')
            checks = []
            for linear_coefficient in [0, 1, 3]:
                intercept = f-linear_coefficient*i
                g = add(constant(intercept), product(constant(linear_coefficient), var('z')))
                H = add(add(power(g, 2), product(constant(Delta*c**4), power(var('z'), 2)), -1), constant(1), -1)
                check(H and sum(coeff*i**len(m) for m, coeff in H.items()) == 0, 'nonzero polynomial with actual component root')
                degree = max(len(m) for m in H)
                leading = H[('z',)*degree]
                lower_max = max([abs(v) for m, v in H.items() if len(m) < degree] or [0])
                check((i-1)*abs(leading) <= lower_max, 'integer Cauchy root estimate')
                checks.append(dict(slope=linear_coefficient, intercept=intercept, H=record(H),
                                   coefficient_norm=sum(abs(v) for v in H.values())))
            components.append(dict(A0=A0, R=R, c=c, D=D, i=i, f=f, root_checks=checks))
    return dict(formal_psi_compositions=compositions, first_odd_term_cases=growth,
        weighted_monomials=monomials, cutoff_cases=thresholds, main_strong_components=components,
        scope='Finite polynomial and inequality corroboration only; no complete native zero or generic G compiler')


def build(root):
    for name, expected in PINS.items():
        check(sha((root/name).read_bytes()) == expected, 'inert dependency pin '+name)
    packet = read(root/'complete84_scaled_strong_output.json')['packet']
    signed = read(root/'complete84_signed_quotient_absorption.json')
    old = read(root/'complete84_strong_root_absorption.json')
    check(len(packet['source']) == 84 and len(packet['free']) == 25, 'complete source/interface')
    check(signed['authenticated_parent_source'] == old['authenticated_source'] == packet['source'], 'same full actual source across inherited proofs')
    check(signed['source_sha256'] == PINS['complete84_signed_quotient_absorption.py'] and old['source_sha256'] == PINS['complete84_strong_root_absorption.py'], 'inherited helper byte bindings')
    check(signed['theorem']['normalized_rank'] == 'c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R', 'normalized Rc rank')
    check(signed['theorem']['old85_bound'] == 'absolute values <c^4' and not signed['theorem']['positive_T_parent_restoration_used'], 'direct signed-domain size statement')
    identities = symbolic_source(packet)
    check(identities == old['source_evidence'], 'recomputed entire sign/zero-root and exterior85 evidence')
    boundary = extended_interface(packet, identities)
    return dict(status='PASS_MULTIPLIER_DEPENDENT_ROOT_ABSORPTION', source_sha256=sha(Path(__file__).read_bytes()),
        pins=PINS, authenticated_source=packet['source'], full_source_evidence=identities,
        extended_interface=boundary, corroboration=corroboration(),
        theorem=dict(domain='Fixed integer polynomial f=G in all88 f/T/y-independent source values',
            sign_map='f=abs(G), T=sign(G)*T, all88 arguments unchanged', zero_G_sector='empty before rank recovery',
            specialized_polynomial='g(z)=G(e85,z,Delta*c^2*z,Delta^2*c^4*z^2)',
            coefficient_norm_bound='||g||_1<=L*c^(6t), deg(g)<=2t',
            root_polynomial='H(z)=g(z)^2-Delta*c^4*z^2-1 is nonzero in Z[z]',
            upper_bound='i<=(L^2+2)*c^max(12t,5)', lower_bound='i>c^(c-1)',
            cutoff='2d*x+b_source<R<c<max(12t,5)+1+ceil(log2(L^2+2))', whole_input_projection='finite'),
        scope=dict(predecessor_execution=False, generic_G_implementation=False, new_paid_circuit=False,
                   new_native_zero_fixture=False, positive_T_restoration_claimed=False, global_minimum_claimed=False))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(result, sort_keys=True, indent=2)+'\n')
    else:
        check(canonical(result) == canonical(read(args.expect)), 'exact type-sensitive receipt')
    print(result['status'], '66 computed+22 supplied values; complete sign/zero-root identities')


if __name__ == '__main__':
    main()
