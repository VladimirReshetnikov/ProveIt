"""Paid central-digit extraction, conditional dot lemma and native FIFO counterexamples."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import input_bridge_boolean_ternary60 as prior


def extraction_rows(left='left', right='right', radix='radix'):
    return [('cp_product', '*', left, right),
            ('cp_upper', '*', radix, 'cp_high'),
            ('cp_shifted', '*', 'q', 'cp_upper'),
            ('cp_rhs', '+', 'cp_low', 'cp_shifted'),
            ('cp_bound', '+', 'cp_low', 'cp_alpha')]


def source65():
    base = prior.source_check(True)
    extra = extraction_rows('F2', 'F3', 3)
    names = base['positive_parameters'] + base['positive_auxiliaries']
    names += ['cp_high', 'cp_low', 'cp_alpha']
    z = {name: sp.Symbol(name) for name in names}
    schedule = base['instructions'] + extra
    env = prior.prior.execute(schedule, dict(z, n2=z['q']))
    equalities = [record['equality'] for record in base['sources']]
    equalities += [('cp_product', 'cp_rhs'), ('cp_bound', 'q')]
    polys = prior.independent_sources(z, True)
    polys += [z['F2']*z['F3']-z['cp_low']-3*z['q']*z['cp_high'],
              z['cp_low']+z['cp_alpha']-z['q']]
    u = 2*z['r']+1+z['j']*z['c']
    correction = polys[8]*(u*u-z['y_aux']**2)
    records = []
    for i, ((left, right), poly) in enumerate(zip(equalities, polys)):
        adjust = correction if i == 9 else 0
        assert sp.expand(env[left]-env[right]-poly-adjust) == 0, i
        records.append(dict(equality=[left, right], source=str(sp.expand(poly)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 65 and counts['*'] == 34
    assert counts['+']+counts['-'] == 31 and len(polys) == 18
    assert len(names)-1 == 30
    assert set().union(*(poly.free_symbols for poly in polys)) == set(z.values())
    return dict(operations=65, multiplications=34, additions_subtractions=31,
                equations=18, positive_witnesses_excluding_x=30,
                instructions=[list(row) for row in schedule], sources=records,
                exact_added_predicate='Positive lower remainder and positive high quotient; the native ternary digit of F2*F3 at q is zero, not necessarily its polynomial convolution coefficient.')


def digits(value, radix, length):
    return [value//radix**i % radix for i in range(length)]


def coefficients(a, b):
    return [sum(a[i]*b[k-i] for i in range(len(a)) if 0 <= k-i < len(b))
            for k in range(len(a)+len(b)-1)]


def dot_checks():
    cases = 0
    rows = []
    for N in range(4, 9):
        radix = N+1
        q = radix**N
        vectors = [[1, 0, *middle, 1] for middle in product((0, 1), repeat=N-3)]
        accepted = 0
        for a, b in product(vectors, repeat=2):
            A = sum(v*radix**i for i, v in enumerate(a))
            B = sum(v*radix**i for i, v in enumerate(b))
            cs = coefficients(a, b)
            dot = sum(a[i]*b[N-i] for i in range(2, N-1))
            low = A*B % q
            high = A*B // (radix*q)
            assert cs[N] == dot and max(cs) <= N < radix
            assert 0 < low < q and high > 0
            assert (A*B == low+radix*q*high) == (dot == 0)
            accepted += dot == 0
            cases += 1
        rows.append(dict(N=N, radix=radix, pairs=len(vectors)**2,
                         zero_dot_pairs=accepted))
    return dict(pairs=cases, domains=rows,
                scope='Conditional typed construction with radix>N and explicit low/high sentinels; varying-radix typing is not implemented.')


def reflection_checks():
    A, B, J, q, radix, H, low, alpha = sp.symbols('A B J q radix H low alpha')
    env = dict(A=A, B=B, J=J, q=q, radix=radix, cp_high=H, cp_low=low, cp_alpha=alpha)
    rows = [('cr_ab', '*', 'A', 'B'), ('cr_sum', '+', 'A', 'B'),
            ('cr_j_sum', '*', 'J', 'cr_sum'), ('cr_twice', '*', 2, 'cr_ab'),
            ('cr_E', '-', 'cr_j_sum', 'cr_twice')]
    rows += extraction_rows()[1:]
    result = prior.prior.execute(rows, env)
    assert sp.expand(result['cr_E']-result['cp_rhs']-
                     (J*(A+B)-2*A*B-low-radix*q*H)) == 0
    assert sp.expand(result['cp_bound']-q-(low+alpha-q)) == 0
    counts = Counter(row[1] for row in rows)
    assert len(rows) == 9 and counts['*'] == 5
    cases = 0
    for N in range(3, 7):
        radix = N+1
        q = radix**N
        J = (q-1)//(radix-1)
        # Explicit endpoint guards make both quotient/remainder coordinates positive.
        for a_mid, b_mid in product(product((0, 1), repeat=N-2), repeat=2):
            a = [1, *a_mid, 0]
            b = [0, *b_mid, 1]
            aa = sum(v*radix**i for i, v in enumerate(a))
            bb = sum(v*radix**i for i, v in enumerate(b))
            E = J*(aa+bb)-2*aa*bb
            mismatch = sum((a[i]-b[N-i])**2 for i in range(1, N))
            expected = []
            for k in range(2*N-1):
                expected.append(sum((a[i]-b[k-i])**2 for i in range(N)
                                    if 0 <= k-i < N))
            assert E == sum(v*radix**i for i, v in enumerate(expected))
            assert expected[N] == mismatch and max(expected) <= N < radix
            low, high = E % q, E//(radix*q)
            assert 0 < low < q and high > 0
            assert (E == low+radix*q*high) == (mismatch == 0)
            cases += 1
    return dict(operations_with_supplied_repunit=9, multiplications=5,
                additions_subtractions=4, equations=2,
                extra_operations_to_construct_repunit=2,
                instructions=[list(row) for row in rows], guarded_pairs=cases,
                scope='Exact reflected-equality test under typed Boolean digits, endpoint guards and radix>N; none of these guards or the varying-radix geometry is obtained for free.')


def fifo_counterexamples():
    rows = []
    for value, x, wanted in ((91, 10, 'false_negative'), (118, 37, 'false_positive')):
        q, W, N, m = 243, 81, 5, 4
        fields = [1, 1, value, value]
        a = digits(value, 3, N)
        cs = coefficients(a, a)
        dot = cs[N]
        lower_polynomial = sum(cs[i]*3**i for i in range(N))
        low, high, digit = value*value % q, value*value//(3*q), value*value//q % 3
        assert all(prior.native_boolean(F, N) for F in fields)
        assert sum(fields) < q and sum(fields) % 2 == 0
        assert 2*value == 2*x+W*2 and 0 < 2*x < W and q == 3*W
        assert prior.run(2*x, 2, m, N) == (2*value, 0)
        r = prior.pack(fields, q)
        assert prior.prior.valuation(r) == 0 and r % 2 == 0
        assert 0 < low < q and high > 0
        assert digit == (dot+lower_polynomial//q) % 3
        assert lower_polynomial//q == 1
        if wanted == 'false_positive':
            assert dot == 2 and digit == 0 and value*value == low+3*q*high
        else:
            assert dot == 0 and digit == 1 and value*value != low+3*q*high
        rows.append(dict(kind=wanted, x=x, q=q, W=W, fields=fields,
                         alpha=q-sum(fields), width_beta=W-2*x, L=3, packed_r=r,
                         low_first_digits=a, convolution_coefficients=cs,
                         central_coefficient=dot, lower_polynomial=lower_polynomial,
                         incoming_carry=1, extracted_digit=digit,
                         cp_low=low, cp_high=high, cp_alpha=q-low,
                         full_positive_extension=('Reviewed Boolean60 supplies every base kernel coordinate; '
                                                  'the false positive also satisfies both added extraction equalities.')))
    return rows


def verify():
    return dict(status='PASS_CENTRAL_PRODUCT_LEDGER_AND_NATIVE_CARRY_OBSTRUCTION',
                source65=source65(), conditional_dot=dot_checks(),
                conditional_reflection=reflection_checks(), counterexamples=fifo_counterexamples(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                scope='Five paid operations extract a radix digit. A zero dot-product interpretation additionally requires proven carry bounds and reflected wiring.',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'], operations=result['source65']['operations'],
                         conditional_dot_pairs=result['conditional_dot']['pairs'],
                         conditional_reflection_pairs=result['conditional_reflection']['guarded_pairs'],
                         full_FIFO_counterexamples=len(result['counterexamples'])), indent=2))
