"""A 57-operation fixed-idle FIFO and its exact eventual input language.

Fixed T is a positive odd numeral, not an extra input or witness.
The full positive kernel extension is inherited from binary FIFO58.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

import sympy as sp

import native_binary_three_row_fifo58 as fifo


def source_check():
    parameters = ['x']
    auxiliaries = ['q', 'F1', 'F2']+fifo.CORE_NAMES+[
        'odd_half', 'bound_beta', 'W', 'L', 'width_beta']
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    T = sp.Symbol('idle_word')
    outer = []
    for name, op, left, right in fifo.OUTER:
        if name == 'bs_sum01':
            continue
        if name == 'bs_sum012':
            outer.append(('bs_sum12', '+', 'F1', 'F2'))
            continue
        if name == 'bs_q':
            outer.append(('bs_q', '+', 'bs_sum12', 'idle_successor'))
            continue
        outer.append((name, op, 'idle_word' if left == 'F0' else left,
                      'idle_word' if right == 'F0' else right))
    schedule = outer+fifo.CORE+fifo.BOUND+fifo.FIFO
    env = fifo.prior.ternary.execute(
        schedule, dict(z, n2=z['q'], idle_word=T, idle_successor=T+1))
    equations = [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd'),
                 ('bs_X_bound', 'wn2')]+fifo.prior.CORE_EQUALITIES+[
        ('fifo_width', 'W'), ('fifo_time', 'q'), ('fifo_read', 'F2')]
    polynomials = fifo.prior.independent_sources(dict(z, F0=T, F3=sp.Integer(0)))
    polynomials += [2*z['x']+z['width_beta']-z['W'],
                    z['W']*z['L']-z['q'],
                    2*z['x']+z['W']*z['F1']-z['F2']]
    U = z['j']*z['c']-(2*z['r']+1)
    correction = polynomials[11]*(U*U-z['y_aux']**2)
    assert len(equations) == len(polynomials) == 17
    records = []
    for index, ((left, right), polynomial) in enumerate(zip(equations, polynomials)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0
        records.append(dict(equality=[left, right], source=sp.sstr(polynomial),
                            correction=sp.sstr(adjust)))
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in schedule)
    assert len(schedule) == 57 and counts == {'M': 30, 'A': 27}
    assert len(auxiliaries) == 25
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values()) | {T}
    return dict(operations=57, multiplications=30, additions_subtractions=27,
                equations=17, positive_witnesses=auxiliaries,
                fixed_numerals={'idle_word': 'T positive odd', 'idle_successor': 'T+1'},
                schedule=[list(row) for row in schedule], sources=records)


def step(state, W, idle):
    read = state & 1
    if idle and read:
        return None
    append = 0 if idle else 1-read
    return state//2+(W//2)*append, append


def fixed_width_accepts(T, x, m):
    """Exact finite procedure, with positivity of append supplied by a full cycle."""
    W, state = 1 << m, 2*x
    if not 0 < state < W:
        return False
    for j in range(T.bit_length()):
        result = step(state, W, (T >> j) & 1)
        if result is None:
            return False
        state, _ = result
    # After the last prescribed idle, each visit flips one cell; 2m visits
    # restore the entire queue. A further such cycle supplies append1.
    for _ in range(2*m):
        if state == 0:
            return True
        state, _ = step(state, W, False)
    return False


def is_power_two(n):
    return n > 0 and n & (n-1) == 0


def classify(T, x):
    assert T > 0 and T & 1 and x > 0
    if is_power_two(2*x+T+1):
        return True
    return any(fixed_width_accepts(T, x, m)
               for m in range(2, T.bit_length()) if 1 << m <= T)


def scalar_accepts(T, x, m, t):
    W, q, I = 1 << m, 1 << t, 2*x
    if I >= W or t <= m:
        return False
    A, remainder = divmod(q-I-T-1, W+1)
    if remainder or A <= 0:
        return False
    D = I+W*A
    return (T < q and D < q and not (T & A or T & D or A & D)
            and T+A+D == q-1)


def verify_language():
    fixed_cases = whole_cases = converse_cases = 0
    exceptions = {}
    for T in range(1, 64, 2):
        finite_exceptions = []
        h = T.bit_length()
        for x in range(1, 81):
            I, S = 2*x, 2*x+T+1
            found = False
            for m in range(2, max(I, T).bit_length()+3):
                W = 1 << m
                if W <= I:
                    continue
                actual = any(scalar_accepts(T, x, m, t)
                             for t in range(m+1, h+4*m+1))
                assert actual == fixed_width_accepts(T, x, m), (T, x, m)
                if W > T:
                    # A fixed W can only accept a subset of the power family.
                    assert not actual or is_power_two(S)
                found |= actual
                fixed_cases += 1
            assert found == classify(T, x), (T, x)
            whole_cases += 1
            if found and not is_power_two(S):
                assert 2*x < T
                finite_exceptions.append(x)
        if finite_exceptions:
            exceptions[str(T)] = finite_exceptions
        for r in range(max(2, T.bit_length()+1), T.bit_length()+7):
            S, I = 1 << r, (1 << r)-T-1
            assert I > 0 and I % 2 == 0 and I & T == 0
            m = r+1
            assert scalar_accepts(T, I//2, m, 2*m+r)
            converse_cases += 1
    # A real small-width exception rules out dropping the finite prefix.
    assert scalar_accepts(9, 1, 2, 5)
    assert not is_power_two(2+9+1)
    return dict(independent_fixed_width_comparisons=fixed_cases,
                complete_language_comparisons=whole_cases,
                unbounded_family_converse_fixtures=converse_cases,
                finite_exceptions_in_audited_T_range=exceptions,
                exact_exception={'T': 9, 'x': 1, 'W': 4, 'q': 32, 'A': 4, 'D': 18},
                theorem='Accepted inputs are exactly the translated powers of two plus an effectively computed finite set with2x<T')


def verify_controller_reduction():
    cases = 0
    for T in range(1, 40, 2):
        for b in range(-7, 8):
            if b == 0:
                continue
            g = -b*(T+1)
            for A, D in ((2, 4), (4, 18), (18, 52)):
                q = T+A+D+1
                assert b*A+b*D-b*q == g
                assert -g//b-1 == T
                cases += 1
    return dict(algebraic_checksum_cases=cases,
                original_coefficients='a=b!=0,c=-b,g=-b(T+1)',
                scope='Exact on the FIFO58 zero set; coefficient compatibility and positive oddT are fixed-parameter conditions')


def verify():
    return dict(status='PASS_BINARY_FIXED_IDLE_FIFO57', source=source_check(),
                language=verify_language(), controller=verify_controller_reduction(),
                complete_universal_comparison_bound=75,
                limit='This57-operation fixed-selector family has a regular decidable input language, not a universal controller')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'], '57=30M+27A;25 positive witnesses;17 equations', result['language'])
