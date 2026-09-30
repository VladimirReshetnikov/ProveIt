"""Scoped polynomial-input obstruction for the exact filtered paired family."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp

import native_controller_paired_filter70 as prior


def affine_source(aligned=False):
    base = prior.source_check(True, aligned, True)
    schedule = []
    for old in base['instructions']:
        name, op, left, right = old
        if name == 'bt_initial':
            assert (op, left, right) == ('*', 2, 'x')
            schedule += [(name, '*', 'input_scale', 'x'),
                         ('poly_initial', '+', name, 'input_offset')]
        else:
            schedule.append((name, op,
                             'poly_initial' if left == 'bt_initial' else left,
                             'poly_initial' if right == 'bt_initial' else right))
    names = base['positive_parameters'] + base['positive_auxiliaries']
    z = {name: sp.Symbol(name) for name in names}
    constants = {name: sp.Symbol(name) for name in
                 ('g0', 'g1', 'g2', 'gap', 'block_modulus', 'input_scale', 'input_offset')}
    env = prior.boolean.prior.execute(schedule, dict(z, **constants, n2=z['q']))
    all_symbols = dict(z, **constants)
    records = []
    sources = []
    for record in base['sources']:
        left, right = record['equality']
        left = 'poly_initial' if left == 'bt_initial' else left
        right = 'poly_initial' if right == 'bt_initial' else right
        original = sp.sympify(record['source'], locals=all_symbols)
        polynomial = sp.expand(original.subs(z['x'],
                               (constants['input_scale']*z['x']+constants['input_offset'])/2))
        sources.append(polynomial)
        correction = sp.sympify(record['correction'], locals=all_symbols)
        assert z['x'] not in correction.free_symbols
        assert sp.expand(env[left]-env[right]-polynomial-correction) == 0
        records.append(dict(equality=[left, right], source=str(polynomial),
                            correction=str(correction)))
    assert sources[14] == constants['input_offset']+constants['input_scale']*z['x']-z['W']+z['width_beta']
    assert sources[16] == -constants['input_offset']-constants['input_scale']*z['x']+z['init0']+z['init1']
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 70+3*aligned
    assert counts['*'] == 35+2*aligned
    assert counts['+']+counts['-'] == 35+aligned
    assert len(records) == 20+2*aligned and len(names)-1 == 29+2*aligned
    return dict(operations=len(schedule), multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(records),
                positive_witnesses_excluding_x=len(names)-1,
                positive_parameters=base['positive_parameters'],
                positive_auxiliaries=base['positive_auxiliaries'],
                input_numerals='input_scale=2c, input_offset=2d; fixed c>=1,d>=0',
                centered_controller='g0*F0+g1*F1+g2*F3=-s, gap=-s',
                instructions=[list(row) for row in schedule], sources=records,
                scope='Exact positive finite-run source; this input substitution does not give a universal family')


def v3(n):
    assert n
    n = abs(n)
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def value(bits):
    return sum(bit*3**i for i, bit in enumerate(bits))


def lift(Q, z, target, n):
    root = 0
    for j in range(n):
        modulus = 3**(j+1)
        candidates = [root+d*3**j for d in range(3)
                      if (int(Q.subs(z, root+d*3**j))-target) % modulus == 0]
        assert len(candidates) == 1
        root = candidates[0]
    return root


def polynomial_checks():
    x,z = sp.symbols('x z')
    polynomials = [2*x, 6*x+8, 2*x*x, 2*(x+1)**3,
                   2*(9*x*x+3*x+7), 2*(x**4+5*x*x+1)]
    rows = []
    permutations = maps = 0
    for P in polynomials:
        derivative = sp.diff(P, x)
        a = next(a for a in range(2, 2*sp.degree(P, x)+6, 2) if derivative.subs(x,a) != 0)
        Da = int(derivative.subs(x,a))
        e = v3(Da)
        v,K = e+1,2*e+1
        Pa = int(P.subs(x,a))
        Q = sp.Poly(sp.expand((P.subs(x,a+3**v*z)-Pa)/3**K), z)
        assert all(c.is_Integer for c in Q.all_coeffs())
        u = Da//3**e
        assert u % 3 and Q.nth(1) == u and Q.nth(0) == 0
        assert all(Q.nth(i) % 3 == 0 for i in range(2, Q.degree()+1))
        for n in range(1,5):
            modulus = 3**n
            assert sorted(int(Q.eval(i)) % modulus for i in range(modulus)) == list(range(modulus))
            for target in range(modulus):
                root = lift(Q.as_expr(),z,target,n)
                assert 0 <= root < modulus and int(Q.eval(root)) % modulus == target
                permutations += 1
        examples = []
        for length in (2,3,5):
            for middle in (0,1):
                continuation = [2]*length+[middle]+[2]*length+[1]
                examples.append(continuation)
            examples.append([2]*length+[0,2,0,1])
        realized = []
        for continuation in examples:
            n = len(continuation)
            residue = Pa % 3**K + 3**K*value(continuation)
            target = ((residue-Pa)//3**K) % 3**n
            root = lift(Q.as_expr(),z,target,n)
            ordinary = a+3**v*root
            if ordinary % 2:
                root += 3**n
                ordinary = a+3**v*root
            actual = int(P.subs(x,ordinary))
            assert ordinary > 0 and ordinary % 2 == 0 and actual > 0 and actual % 2 == 0
            assert actual % 3**(K+n) == residue
            assert [actual//3**(K+i) % 3 for i in range(n)] == continuation
            assert actual >= 3**(K+n-1)
            maps += 1
            if len(realized) < 2:
                realized.append(dict(continuation=continuation, ordinary_even_x=ordinary,
                                     input_value=actual, prefix_length=K+n))
        rows.append(dict(polynomial=str(sp.expand(P)), even_base=a, derivative_valuation=e,
                         fixed_low_trits=K, lift_polynomial=str(Q.as_expr()), examples=realized))
    return dict(polynomials=rows, exact_residue_lifts=permutations,
                prescribed_continuation_maps=maps,
                scope='Symbolic Taylor divisibility and finite exact lifting; the proof covers every nonconstant integer polynomial')


def contraction_checks():
    cases = admitted = alternatives = 0
    for gamma in range(-10,11):
        for C in range(max(1,abs(gamma)),max(1,abs(gamma))+5):
            L = 1
            while 3**L <= 2*C+abs(gamma):
                L += 1
            for initial in range(-C,C+1):
                k = initial
                integral = True
                for _ in range(L):
                    if (k+gamma) % 3:
                        integral = False
                        break
                    k = (k+gamma)//3
                if integral:
                    assert 2*initial == gamma and 2*k == gamma
                    admitted += 1
                cases += 1
    for g0,g1,g2 in product(range(-8,9),repeat=3):
        zero_test = g2 in (g0,g1)
        one_test = g2 in (0,g0+g2,g1+g2)
        if zero_test and one_test:
            if g2:
                assert {g0,g1} == {0,g2}
            else:
                assert g0 == 0 or g1 == 0
            alternatives += 1
    return dict(long_two_run_initial_states=cases, integral_paths=admitted,
                local_coefficient_triples=17**3, admitted_coefficient_alternatives=alternatives,
                scope='Exact contraction and local transitions; not an enumeration of accepted queue languages')


def zero_orbit_checks():
    rows = []
    for m in range(1,9):
        zero = (0,)*m
        def step(bits):
            return bits[1:]+(1-bits[0],)
        orbit = set()
        current = zero
        while current not in orbit:
            orbit.add(current)
            current = step(current)
        assert current == zero and len(orbit) == 2*m
        one_switch = {(0,)*r+(1,)*(m-r) for r in range(m+1)}
        one_switch |= {(1,)*r+(0,)*(m-r) for r in range(m+1)}
        assert orbit == one_switch
        rejected010 = 0
        for bits in product((0,1),repeat=m):
            current = bits
            reaches_zero = False
            for _ in range(2*m):
                if current == zero:
                    reaches_zero = True
                current = step(current)
            assert current == bits
            assert reaches_zero == (bits in one_switch)
            if bits[:3] == (0,1,0):
                assert not reaches_zero
                rejected010 += 1
        rows.append(dict(width=m, binary_words=2**m, zero_orbit_size=len(orbit),
                         forced_prefix010_rejections=rejected010))
    return dict(domains=rows, all_binary_words=sum(r['binary_words'] for r in rows),
                scope='Complete finite zero-basin check for the secondary-append-zero case')


def linear_filter_reduction():
    f0,f1,f2,f3,q,H = sp.symbols('F0 F1 F2 F3 q H')
    r0,r1,r2,r3,rq,c = sp.symbols('r0 r1 r2 r3 rq c')
    raw = r0*f0+r1*f1+r2*f2+r3*f3+rq*q-c
    reduced = (r0-r2)*f0+(r1-r2)*f1+r3*f3+(r2+2*rq)*H-(c-rq)
    assert sp.expand(raw.subs({f2:H-f0-f1,q:2*H+1})-reduced) == 0
    collapsed = raw.subs({r0:-2*rq,r1:-2*rq,r2:-2*rq,r3:0,c:rq})
    assert sp.expand(collapsed-rq*(q-1-2*(f0+f1+f2))) == 0
    return dict(reduced_row=str(sp.expand(reduced)),
                necessary_coefficients_if_all_even_inputs_accepted='r0=r1=r2=-2*rq; r3=0; c=rq',
                collapsed_row=str(sp.expand(collapsed)),
                scope='Fixed affine equalities in four whole stream words and q; no added witnesses, widths, inequalities or nonlinear relations')


def verify():
    return dict(status='PASS_FILTERED_PAIRED_POLYNOMIAL_INPUT_OBSTRUCTION',
                sources=dict(affine70=affine_source(),aligned_affine73=affine_source(True)),
                polynomial_images=polynomial_checks(), contractions=contraction_checks(),
                zero_orbits=zero_orbit_checks(), linear_filters=linear_filter_reduction(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                theorem='For every fixed positive even integer-polynomial input substitution in this one-carry family, containing all positive even x implies containing all positive x',
                scope='Allows finite affine carry conjunctions and fixed linear field/q equalities; no richer filters or other appearances of x; no general decidability assertion',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('sources','polynomial_images')},indent=2))
