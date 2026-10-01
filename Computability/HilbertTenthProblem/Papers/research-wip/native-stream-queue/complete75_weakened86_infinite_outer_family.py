"""Infinite low-X first/main/transport families for the unchanged86 candidate.

An exact directed-integer interval certificate validates one large-index
outer tuple without materializing its enormous Pell coordinates.  No input
norm, full index congruence, or complete candidate zero is asserted.
"""
import argparse
import json
from pathlib import Path
import random
import sympy as sp

import complete75_weakened86_auxiliary_sign_lift as auxiliary

pell = auxiliary.pell
candidate = auxiliary.candidate


class IntegerIntervals:
    """Outward-rounded positive integer intervals m*2^e, using only integers."""

    def __init__(self, bits):
        assert bits >= 8
        self.bits = bits

    def normalize(self, m, e, upper):
        assert m >= 0 and e >= 0
        while m.bit_length() > self.bits:
            shift = m.bit_length()-self.bits
            m = (m+(1 << shift)-1) >> shift if upper else m >> shift
            e += shift
        return (m, e) if m else (0, 0)

    @staticmethod
    def rounded_shift(m, shift, upper):
        assert m >= 0 and shift >= 0
        if shift == 0:
            return m
        if shift >= m.bit_length():
            return int(bool(m) and upper)
        return (m+(1 << shift)-1) >> shift if upper else m >> shift

    def endpoint_add(self, x, y, upper):
        exponent = max(x[1], y[1])
        mantissa = self.rounded_shift(x[0], exponent-x[1], upper)
        mantissa += self.rounded_shift(y[0], exponent-y[1], upper)
        return self.normalize(mantissa, exponent, upper)

    def endpoint_mul(self, x, y, upper):
        return self.normalize(x[0]*y[0], x[1]+y[1], upper)

    def exact(self, n):
        assert n >= 0
        return self.normalize(n, 0, False), self.normalize(n, 0, True)

    def add(self, x, y):
        return (self.endpoint_add(x[0], y[0], False),
                self.endpoint_add(x[1], y[1], True))

    def mul(self, x, y):
        return (self.endpoint_mul(x[0], y[0], False),
                self.endpoint_mul(x[1], y[1], True))

    @staticmethod
    def compare(x, y):
        """Exact endpoint order without expanding its potentially huge exponent."""
        if x[0] == 0 or y[0] == 0:
            return (x[0] > y[0])-(x[0] < y[0])
        bx, by = x[0].bit_length()+x[1], y[0].bit_length()+y[1]
        if bx != by:
            return 1 if bx > by else -1
        # Equal total bit lengths bound the shift by the mantissa sizes.
        exponent = min(x[1], y[1])
        xx, yy = x[0] << (x[1]-exponent), y[0] << (y[1]-exponent)
        return (xx > yy)-(xx < yy)

    def pell(self, A, index):
        assert A >= 2 and index >= 0
        delta = self.exact(A*A-1)
        def product(left, right):
            x, y = left
            u, v = right
            return (self.add(self.mul(x, u), self.mul(delta, self.mul(y, v))),
                    self.add(self.mul(x, v), self.mul(y, u)))
        answer, base = (self.exact(1), self.exact(0)), (self.exact(A), self.exact(1))
        while index:
            if index & 1:
                answer = product(answer, base)
            index //= 2
            if index:
                base = product(base, base)
        return answer


def family_data(d):
    assert d >= 4
    q = 1 << d
    e = 3*d if d % 2 else 3*d+1
    X, Y = 1 << e, q**3
    a, A, P = Y*(X+1), Y*(X+1)+2, 2*X*Y*Y+1
    H = 4*a+3
    delta_A, delta_P = A*A-1, P*P-1
    alpha = q-2-2*d
    assert e % 2 and e >= 13 and X % q**3 == 0 and Y == q**3
    assert X//q**3 in (1, 2) and alpha > 0
    assert delta_A % 2 and (delta_P & -delta_P).bit_length()-1 == e+6*d+2
    assert (e+6*d+2) % 2
    assert A < P < 2*A*A-1
    assert pell(A, 3)[1] > X+2*H
    N = ((12*(Y+1)).bit_length()+1)//2
    assert 3**(2*N) > 12*(Y+1)
    return dict(d=d, B=q, q=q, Jrep=1, X=X, Y=Y, w=X//q**3, s=1, exponent=e,
        a=a, A=A, P=P, H=H, E=X*Y, Delta_A=delta_A, Delta_P=delta_P,
        valuation_2_Delta_P=e+6*d+2, x=1, F=2, alpha=alpha, zplus=1, C=0,
        transport_sign=-1, conjugate_error_index_threshold=N)


def certify_large_tuple(bits=128):
    data = family_data(4)
    p, n, T, progression_index = 321629343237, 214421015143, 8758492, 18361
    assert pow(2, T, data['H']) == 1
    assert p == data['exponent']+2*T*progression_index
    assert pow(2, p, data['H']) == data['X']
    assert n < p < 2*n and p % 2 and p > data['exponent']
    arithmetic = IntegerIntervals(bits)
    c = arithmetic.pell(data['A'], p)[1]
    k = arithmetic.mul(arithmetic.exact(2), arithmetic.pell(data['P'], n)[1])
    lower_ratio = arithmetic.mul(k, arithmetic.exact(data['Y']))
    upper_ratio = arithmetic.mul(k, arithmetic.exact(data['Y']+1))
    assert arithmetic.compare(c[0], lower_ratio[1]) > 0
    assert arithmetic.compare(c[1], upper_ratio[0]) < 0
    assert c[0][0].bit_length()+c[0][1] == c[1][0].bit_length()+c[1][1]
    return dict(precision_bits=bits, p=p, n=n, odd_gap=2*n-p, main_return_period=T,
        progression_index=progression_index, exact_main_residue=data['X'],
        main_psi_interval=c, first_kY_interval=lower_ratio,
        first_kY_plus_k_interval=upper_ratio,
        exact_c_bit_length=c[0][0].bit_length()+c[0][1],
        both_strict_ratios_certified=True, target_signs=auxiliary.allowed_signs(p),
        scope='Exact first/main/transport outer tuple only. Pell coordinates are enclosed, not materialized; '
              'no input norm, first-index completion or full86 zero is asserted.')


def interval_audit():
    rng = random.Random(8618321)
    operations = pell_cases = 0
    def value(endpoint):
        return endpoint[0] << endpoint[1]
    for bits in (8, 16, 32, 64, 128):
        intervals = IntegerIntervals(bits)
        for _ in range(128):
            x = (rng.randrange(0, 1 << 80), rng.randrange(0, 200))
            y = (rng.randrange(0, 1 << 80), rng.randrange(0, 200))
            for upper in (False, True):
                s = value(intervals.endpoint_add(x, y, upper))
                m = value(intervals.endpoint_mul(x, y, upper))
                if upper:
                    assert s >= value(x)+value(y) and m >= value(x)*value(y)
                else:
                    assert s <= value(x)+value(y) and m <= value(x)*value(y)
                operations += 2
            assert intervals.compare(x, y) == ((value(x) > value(y))-(value(x) < value(y)))
        for A in (2, 3, 17, 256, 65537):
            for index in (0, 1, 2, 3, 7, 16, 31, 127, 255, 1024):
                expected = pell(A, index)
                bounded = intervals.pell(A, index)
                for integer, (lo, hi) in zip(expected, bounded):
                    assert value(lo) <= integer <= value(hi)
                pell_cases += 1
    return dict(directed_integer_operation_bounds=operations,
        exact_endpoint_order_checks=640, exact_materialized_Pell_pairs=pell_cases,
        precision_choices=[8, 16, 32, 64, 128])


def source_identities():
    """Actual literal first/main/transport rows with symbolic Pell roots."""
    data = family_data(4)
    chi_first, chi_main, k, c = sp.symbols('chi_first chi_main k c')
    Y, X, a, H = (data[n] for n in ('Y', 'X', 'a', 'H'))
    values = {n: sp.Integer(1) for n in candidate.RETAINED+['x']}
    values.update(Jrep=1, x=1, F=2, alpha=6, zplus=1, w=2, s=1,
        eta=c-k*Y, zeta=k*(Y+1)-c,
        tau_gap=chi_first-X*Y*Y*k, rho=1, sigma=(chi_main-a*c-X)/H-1)
    fixed = dict(B=16, DC=3, DR=5, MC=10, MF=12, cell_bits=4, inner_bits=3)
    env = candidate.eliminated.fixed_inputs({**values, **fixed})
    nodes = {name: (op, aa, bb) for name, op, aa, bb in candidate.sources()[3]}
    selected = []
    def visit(name):
        if isinstance(name, int) or name in env:
            return
        op, aa, bb = nodes[name]
        visit(aa)
        visit(bb)
        u, v = (env[t] if isinstance(t, str) else t for t in (aa, bb))
        env[name] = u+v if op == '+' else u-v if op == '-' else u*v
        selected.append((name, op, aa, bb))
    for name in ('norm_first', 'norm_main', 'norm_transport'):
        visit(name)
    L = X*Y*Y
    assert sp.expand(env['norm_first']-(chi_first**2-L*(L+1)*k*k)) == 0
    assert sp.expand(env['norm_main']-(chi_main**2-data['Delta_A']*c*c)) == 0
    assert sp.expand(env['norm_transport']+1) == 0
    assert data['P']**2-1 == 4*L*(L+1)
    return dict(literal_rows=selected, symbolic_factor_identities=3,
        factors=['norm_first=1 for k=2*psi_P(n)', 'norm_main=1 for c=psi_A(p)',
                 'norm_transport=-1'],
        scope='Symbolic identities of these three actual factors only; the complete output is not asserted zero.')


def family_audit():
    records = [family_data(d) for d in range(4, 25)]
    # Exact main-root congruence and quotient positivity, on modest hosts.
    congruences = 0
    for d in (4, 5, 7):
        data = family_data(d)
        for p in range(3, 52, 2):
            chi, psi = pell(data['A'], p)
            root = chi-data['a']*psi
            assert (root-pow(2, p, data['H'])) % data['H'] == 0
            assert root > data['X']+2*data['H']
            congruences += 1
    return dict(widths=records, exact_main_residue_and_growth_checks=congruences,
        scope='Width/growth fixtures supplement the all-width proof; they do not assert the ratio at every checked index.')


def verify():
    low, high = certify_large_tuple(96), certify_large_tuple(128)
    for key in ('main_psi_interval', 'first_kY_interval', 'first_kY_plus_k_interval'):
        assert IntegerIntervals.compare(high[key][0], low[key][0]) >= 0
        assert IntegerIntervals.compare(high[key][1], low[key][1]) <= 0
    return dict(status='PASS_INFINITE_LOW_X_OUTER_FAMILY',
        source=auxiliary.residues.inherited.source_contract(),
        family=family_audit(), interval_arithmetic=interval_audit(),
        exact_large_outer_certificates=[low, high], actual_source_identities=source_identities(),
        conclusion='For every fixed compiler width d>=4, the specified fixed q,X,Y and transport data '
                   'admit infinitely many exact first/main Pell ratio solutions with unbounded odd gaps.',
        scope='This refutes a uniform p or gap cutoff from those outer equations alone. '
              'The input norm, retained first-index congruence and complete86 zero problem remain open; '
              'no passing full negative-input CRT class or false-input zero is claimed.')


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
    print(result['status'])
    print(result['conclusion'])
    print(result['scope'])
