"""Exact leading-monomial certificate for a stored arithmetic DAG.

The coefficient domain is Z[beta,K0,MC,MF,cone_A,cone_B].  Huge fixed
numerals and their powers are never materialized.  A cancellation of a
leading term fails this certificate rather than guessing the next term.
The two actual whole circuits need no such fallback.
"""
from collections import defaultdict
import hashlib

PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def leading_certificate(packet):
    names = ['T']+sorted(v for v in packet['variables'] if v != 'T')
    zero_m = (0,)*len(names)
    zero_c = (0,)*len(PORTS)
    values = []
    max_coefficient_support = 0

    def plus(left, right, sign):
        if left is None:
            return None if right is None else (right[0], {m: sign*c for m, c in right[1].items()})
        if right is None:
            return left
        lm, lc = left; rm, rc = right
        lk, rk = (sum(lm), lm), (sum(rm), rm)
        if lk > rk:
            return left
        if rk > lk:
            return rm, {m: sign*c for m, c in rc.items()}
        out = dict(lc)
        for m, c in rc.items():
            out[m] = out.get(m, 0)+sign*c
        out = {m: c for m, c in out.items() if c}
        require(out, 'leading cancellation needs a larger certificate; do not infer a lower term')
        return lm, out

    for node in packet['nodes']:
        kind = node[0]
        if kind == 'integer':
            value = (zero_m, {zero_c: node[1]}) if node[1] else None
        elif kind == 'coefficient':
            power = list(zero_c); power[PORTS.index(node[1])] = 1
            value = zero_m, {tuple(power): 1}
        elif kind == 'variable':
            power = list(zero_m); power[names.index(node[1])] = 1
            value = tuple(power), {zero_c: 1}
        else:
            left, right = values[node[1]], values[node[2]]
            if kind == 'mul':
                if left is None or right is None:
                    value = None
                else:
                    monomial = tuple(a+b for a, b in zip(left[0], right[0]))
                    coefficient = defaultdict(int)
                    for u, a in left[1].items():
                        for v, b in right[1].items():
                            coefficient[tuple(x+y for x, y in zip(u, v))] += a*b
                    coefficient = {m: c for m, c in coefficient.items() if c}
                    require(coefficient, 'product in the formal coefficient domain is nonzero')
                    value = monomial, coefficient
            else:
                require(kind in ('add', 'sub'), 'arithmetic gate')
                value = plus(left, right, 1 if kind == 'add' else -1)
        values.append(value)
        if value is not None:
            max_coefficient_support = max(max_coefficient_support, len(value[1]))

    monomial, coefficient = values[packet['output']]
    actual_monomial = {v: e for v, e in zip(names, monomial) if e}
    certificate = packet['degree_certificate']
    expected = certificate['coefficient']
    require(actual_monomial == certificate['monomial'], 'actual child leading monomial')
    beta_power = (expected['beta'], 0, 0, 0, 0, 0)
    scalar = 2**expected['2']*3**expected['3']
    require(coefficient == {beta_power: scalar}, 'actual child leading coefficient over formal ports')
    require(sum(monomial) == packet['exact_degree'], 'actual exact degree')
    return dict(method='Graded lexicographic leading term at every stored child gate over Z[six formal ports]; T has first priority.',
        variable_order=names, monomial=actual_monomial, exact_degree=sum(monomial),
        coefficient_factorization=expected,
        small_scalar_bits=scalar.bit_length(), small_scalar_hex_sha256=hashlib.sha256(hex(scalar).encode()).hexdigest(),
        coefficient_support=1, maximum_intermediate_coefficient_support=max_coefficient_support,
        no_leading_cancellation=True,
        specialization='The final coefficient uses beta only and is positive at the authentic beta>0, so exact degree survives all six fixed-value substitutions.')
