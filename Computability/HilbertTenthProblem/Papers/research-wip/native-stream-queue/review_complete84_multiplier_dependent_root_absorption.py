"""Independent source/weight/Pell checks; all author and predecessor code stays inert."""
import argparse
import hashlib
import json
from math import comb, isqrt
from pathlib import Path

AUTHOR = {
 'complete84_multiplier_dependent_root_absorption.py': '4fbb8595e4956f43829f91e42a57836bc726c3261bc5f9abf0b473d2493e80c4',
 'complete84_multiplier_dependent_root_absorption.json': '720c602d9d82d456fd50fb9b5c4f66132e6b4ca1222c9832694ddf0d9b92a46b',
 'complete84_multiplier_dependent_root_absorption.md': '045a1147a09d3d70550c9f5c6dcf398d8c9686dbfa957f00d263fb868a485d75',
}
SOURCE = '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'

def require(ok, label):
    if not ok:
        raise ValueError(label)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def encode(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode()

def load(path):
    def unique(items):
        out = {}
        for key, value in items:
            require(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    def reject(value):
        raise ValueError('noninteger JSON number '+value)
    return json.loads(path.read_text(), object_pairs_hook=unique,
                      parse_float=reject, parse_constant=reject)

def scalar(value):
    return {(): value} if value else {}

def variable(name):
    return {(name,): 1}

def add(left, right, sign=1):
    out = dict(left)
    for term, coefficient in right.items():
        out[term] = out.get(term, 0)+sign*coefficient
    return {term: c for term, c in out.items() if c}

def mul(left, right):
    out = {}
    for a, c in left.items():
        for b, d in right.items():
            term = tuple(sorted(a+b))
            out[term] = out.get(term, 0)+c*d
    return {term: c for term, c in out.items() if c}

def product(*items):
    out = scalar(1)
    for item in items:
        out = mul(out, item)
    return out

def power(value, exponent):
    return product(*[value for _ in range(exponent)])

def records(value):
    return [[list(term), coefficient] for term, coefficient in sorted(value.items())]

def closed_pell(n, odd):
    # Direct even/odd binomial formula, not the author's recurrence.
    A = variable('a0')
    disc = add(power(A, 2), scalar(1), -1)
    out = {}
    for k in range(1 if odd else 0, n+1, 2):
        out = add(out, product(scalar(comb(n, k)), power(A, n-k), power(disc, k//2)))
    return out

def compose(outer, inner):
    out = {}
    for term, coefficient in outer.items():
        require(set(term) <= {'a0'}, 'univariate formal Pell polynomial')
        out = add(out, product(scalar(coefficient), power(inner, len(term))))
    return out

def pair_power(A, n):
    # Binary powering in Z[sqrt(A^2-1)], independently of both recurrences.
    disc = A*A-1
    def pair_mul(a, b):
        return a[0]*b[0]+disc*a[1]*b[1], a[0]*b[1]+a[1]*b[0]
    answer, base = (1, 0), (A, 1)
    while n:
        if n & 1:
            answer = pair_mul(answer, base)
        base = pair_mul(base, base)
        n //= 2
    return answer

def ceiling_log2(n):
    result = 0
    while 2**result < n:
        result += 1
    return result

def inspect_source(packet, receipt, signed, old):
    rows, supplied = packet['source'], packet['free']
    require(len(rows) == 84 and len(supplied) == 25 and len(set(supplied)) == 25,
            'literal complete source and supplied interface')
    require(sum(row[1] == '*' for row in rows) == 47, 'unchanged 47M37A ledger')
    require(rows == receipt['authenticated_source'] == old['authenticated_source']
            == signed['authenticated_parent_source'], 'all84 literal rows across dependencies')
    definitions, dependencies = {}, {name: {name} for name in supplied}
    for row in rows:
        require(type(row) is list and len(row) == 4, 'four-entry row')
        name, op, a, b = row
        require(type(name) is str and name not in dependencies and op in ['+', '-', '*'], 'SSA/opcode')
        require(all(type(v) is int or type(v) is str and v in dependencies for v in (a, b)), 'topology')
        definitions[name] = row
        dependencies[name] = set().union(*(dependencies[v] for v in (a, b) if type(v) is str))
    live = set()
    def trace(name):
        if type(name) is int or name in live:
            return
        live.add(name)
        if name in definitions:
            trace(definitions[name][2]); trace(definitions[name][3])
    trace(packet['output'])
    require(live == set(dependencies), 'all84 rows and25 supplied ports live')
    four = {'i', 'f', 'auxiliary_quotient', 'y_aux'}
    three = four-{'i'}
    old_computed = [r[0] for r in rows if not dependencies[r[0]] & four]
    old_supplied = [n for n in supplied if n not in four]
    computed = [r[0] for r in rows if not dependencies[r[0]] & three]
    free = [n for n in supplied if n not in three]
    excluded = [r[0] for r in rows if dependencies[r[0]] & three]
    require(tuple(map(len, (old_computed, old_supplied, computed, free, excluded))) == (64, 21, 66, 22, 18), 'full85/88 partitions')
    require(old_computed == signed['census']['old_computed'] and old_supplied == signed['census']['old_free'], 'signed lemma exact85 names')
    require(set(computed)-set(old_computed) == {'aux_coefficient_root', 'R16'} and set(free)-set(old_supplied) == {'i'}, 'precise extension')
    for operand, expected in [
        ('f', [['L16', '*', 'f', 'f'], ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']]),
        ('auxiliary_quotient', [['auxiliary_Tf', '*', 'auxiliary_quotient', 'f']])]:
        require([r for r in rows if operand in r[2:]] == expected, 'complete direct sign consumers')
    guards = [
        ['wn2', '*', 'w', 'q'], ['sn2', '*', 's', 'n2'], ['UM', '*', 'wn2', 'sn2'],
        ['R12', '+', 'UM', 'sn2'], ['a_square', '*', 'R12', 'R12'],
        ['a4', '*', 4, 'R12'], ['a4m5', '+', 'a4', 3], ['A', '+', 'a_square', 'a4m5'],
        ['c2', '*', 'R10a', 'R10a'], ['Ac2', '*', 'A', 'c2'],
        ['aux_coefficient_root', '*', 'i', 'Ac2'], ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
        ['scaled_f_square', '*', 'A', 'L16'], ['norm_strong', '-', 'scaled_f_square', 'R16']]
    for row in guards:
        require(definitions[row[0]] == row, 'literal coefficient/discriminant producer')
    factors = ['norm_first', 'norm_main', 'norm_input', 'norm_index', 'norm_transport']
    cuts = ['A', 'R10a', 'r_lhs']+factors
    require(set(cuts) <= set(old_computed), 'valid actual exterior cuts')
    reached = set()
    def evaluator(initial):
        memo = dict(initial)
        def at(name):
            if type(name) is int:
                return scalar(name)
            if name not in memo:
                reached.add(name)
                _, op, a, b = definitions[name]
                a, b = at(a), at(b)
                memo[name] = mul(a, b) if op == '*' else add(a, b, 1 if op == '+' else -1)
            return memo[name]
        return at
    def full_source(sign, zero=False):
        start = {n: variable(n) for n in supplied+cuts}
        start['f'] = {} if zero else product(scalar(sign), variable('f'))
        start['auxiliary_quotient'] = product(scalar(sign), variable('auxiliary_quotient'))
        return evaluator(start)(packet['output'])
    full, reversed_sign, zero = full_source(1), full_source(-1), full_source(1, True)
    Delta, c, R, i, f, T, y = [variable(n) for n in ['A', 'R10a', 'r_lhs', 'i', 'f', 'auxiliary_quotient', 'y_aux']]
    P5 = product(*(variable(n) for n in factors))
    Q = product(power(Delta, 2), power(i, 2), power(c, 4))
    V = add(add(product(c, T, f), c, -1), product(R, f, f), -1)
    Na = add(product(Q, add(power(V, 2), power(y, 2), -1)), power(y, 2))
    Ns = add(product(Delta, f, f), Q, -1)
    require(full == reversed_sign == add(product(P5, Na, Ns), Delta, -1), 'all-ring output and sign identity')
    Na0 = add(product(Q, add(power(c, 2), power(y, 2), -1)), power(y, 2))
    zero_expected = product(scalar(-1), Delta, add(product(Delta, i, i, power(c, 4), P5, Na0), scalar(1)))
    require(zero == zero_expected and len(full) == 17 and len(zero) == 4 and len(reached) == 24, 'exact zero sector/24 ancestors')
    require(all('f' not in m and 'auxiliary_quotient' not in m for m in zero), 'zero-f quotient disappearance')
    evidence = dict(computed_exterior=old_computed, supplied_exterior=old_supplied, exact_cut_names=cuts,
        expanded_output_ancestors=[r for r in rows if r[0] in reached], full_coefficients=records(full),
        zero_f_coefficients=records(zero), full_sign_identity=True, full_zero_root_identity=True)
    require(encode(evidence) == encode(receipt['full_source_evidence']) == encode(old['source_evidence']), 'every source evidence field')
    # Expand from actual Delta,c,i cuts, not from a freely supplied Ac2 coefficient.
    start = {n: variable(n) for n in old_computed+old_supplied if n not in ['c2', 'Ac2']}
    start['i'] = variable('z')
    at = evaluator(start)
    S, S2 = at('aux_coefficient_root'), at('R16')
    require(S == product(Delta, power(c, 2), variable('z')) and
            S2 == product(power(Delta, 2), power(c, 4), power(variable('z'), 2)), 'literal S and S2 coefficient expansion')
    weights = [dict(name=n, coefficient_c_exponent=4, z_degree=0) for n in old_computed+old_supplied]
    weights += [dict(name=n, coefficient_c_exponent=w, z_degree=d) for n, w, d in
                [('i', 0, 1), ('aux_coefficient_root', 3, 1), ('R16', 6, 2)]]
    require(len(weights) == len({v['name'] for v in weights}) == 88, 'all88 distinct named weights')
    interface = dict(computed=computed, supplied=free, excluded_computed=excluded,
        added_computed=[definitions[n] for n in ['aux_coefficient_root', 'R16']],
        multiplier_polynomials=dict(S=records(S), S_squared=records(S2)), pointwise_argument_weights=weights)
    require(encode(interface) == encode(receipt['extended_interface']), 'complete88 interface and weights')
    return evidence, interface

def corroborate(saved):
    chi = [closed_pell(n, False) for n in range(37)]
    psi = [closed_pell(n, True) for n in range(37)]
    compositions = []
    for r in range(1, 7):
        for s in range(1, 7):
            value = mul(psi[r], compose(psi[s], chi[r]))
            require(value == psi[r*s], 'closed-binomial normalized psi composition')
            compositions.append([r, s, len(value)])
    growth = []
    for D in range(2, 10):
        for n in range(2, 17):
            value = sum(a*D**len(m) for m, a in psi[n].items())
            require(value == pair_power(D, n)[1] and value >= n*D**(n-1), 'odd first-binomial bound')
            growth.append([D, n, value])
    weights = []
    for de in range(9):
        for di in range(9-de):
            for ds in range(9-de-di):
                for dq in range(9-de-di-ds):
                    t = de+di+ds+dq
                    weight, degree = 4*de+3*ds+6*dq, di+ds+2*dq
                    require(weight <= 6*t and degree <= 2*t, 'coefficient norm and z-degree per monomial')
                    weights.append([de, di, ds, dq, weight, degree])
    cutoffs = []
    for t in range(9):
        for L in [1, 2, 3, 4, 7, 8, 9, 16, 17, 255, 256, 257]:
            K, b = L*L+2, max(12*t, 5)
            cutoff = b+1+ceiling_log2(K)
            for c in [cutoff, cutoff+1]:
                require(L*L*c**(12*t)+c**5+2 <= K*c**b <= c**(c-1), 'both exact cutoff endpoint inequalities')
            cutoffs.append([t, L, b, K, cutoff])
    components = []
    for A0 in range(2, 5):
        for R in range(2, 5):
            D, c = pair_power(A0, R)
            f, ordinate = pair_power(A0, R*c)
            Delta = A0*A0-1
            require(ordinate % (c*c) == 0, 'normalized component multiplier integral')
            i = ordinate//(c*c)
            require(f*f-Delta*c**4*i*i == 1 and D > c and i >= D**(c-1) > c**(c-1), 'component norm and stronger multiplier growth')
            require(isqrt(Delta*c**4)**2 != Delta*c**4, 'component nonsquare coefficient')
            checks = []
            for slope in [0, 1, 3]:
                intercept = f-slope*i
                # Build quadratic coefficients directly, not by the author's polynomial multiplication.
                coeffs = [intercept*intercept-1, 2*slope*intercept, slope*slope-Delta*c**4]
                H = {('z',)*j: coefficient for j, coefficient in enumerate(coeffs) if coefficient}
                require(H and sum(a*i**len(m) for m, a in H.items()) == 0, 'actual integer root of nonzero H')
                degree = max(len(m) for m in H)
                leading = H[('z',)*degree]
                lower = max([abs(a) for m, a in H.items() if len(m) < degree] or [0])
                require((i-1)*abs(leading) <= lower, 'exact integer Cauchy inequality')
                checks.append(dict(slope=slope, intercept=intercept, H=records(H), coefficient_norm=sum(abs(a) for a in H.values())))
            components.append(dict(A0=A0, R=R, c=c, D=D, i=i, f=f, root_checks=checks))
    result = dict(formal_psi_compositions=compositions, first_odd_term_cases=growth, weighted_monomials=weights,
                  cutoff_cases=cutoffs, main_strong_components=components,
                  scope='Finite polynomial and inequality corroboration only; no complete native zero or generic G compiler')
    require(encode(result) == encode(saved), 'every saved finite corroboration record')
    return result

def build(root, author):
    for name, expected in AUTHOR.items():
        require(digest((author/name).read_bytes()) == expected, 'frozen author pin '+name)
    receipt = load(author/'complete84_multiplier_dependent_root_absorption.json')
    require(receipt['source_sha256'] == AUTHOR['complete84_multiplier_dependent_root_absorption.py'], 'author helper-byte binding')
    require(len(receipt['pins']) == 9 and receipt['pins']['complete84_scaled_strong_output.json'] == SOURCE, 'nine direct dependencies')
    for name, expected in receipt['pins'].items():
        require(digest((root/name).read_bytes()) == expected, 'inert dependency pin '+name)
    packet = load(root/'complete84_scaled_strong_output.json')['packet']
    signed = load(root/'complete84_signed_quotient_absorption.json')
    old = load(root/'complete84_strong_root_absorption.json')
    for stem, data in [('complete84_signed_quotient_absorption', signed), ('complete84_strong_root_absorption', old)]:
        require(data['source_sha256'] == receipt['pins'][stem+'.py'], 'inherited helper binding')
    require(signed['theorem']['normalized_rank'] == 'c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R', 'required direct normalized rank')
    require(signed['theorem']['old85_bound'] == 'absolute values <c^4' and not signed['theorem']['positive_T_parent_restoration_used'], 'precise signed-domain bounds')
    evidence, interface = inspect_source(packet, receipt, signed, old)
    finite = corroborate(receipt['corroboration'])
    return dict(status='PASS_INDEPENDENT_MULTIPLIER_DEPENDENT_ROOT_ABSORPTION',
        source_sha256=digest(Path(__file__).read_bytes()), author_pins=AUTHOR, inert_pins=receipt['pins'],
        authenticated_source=packet['source'], unchanged_counts=dict(total=84, M=47, A=37, supplied=25),
        full_source_evidence=evidence, extended_interface=interface, independent_corroboration=finite,
        scope=dict(frozen_code_executed=False, full_native_zero_constructed=False,
                   generic_G_circuit_emitted=False, exact84_degree_reaudited=False,
                   source_sign_zero_and_weights_checked=True, quantified_proof_review_in_companion=True))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--author-root', type=Path)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root, args.author_root or args.root)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(result, sort_keys=True, indent=2)+'\n')
    else:
        require(encode(result) == encode(load(args.expect)), 'exact type-sensitive independent receipt')
    print(result['status'], 'all84 rows; 66+22 boundary; literal S/S2 weights')

if __name__ == '__main__':
    main()
