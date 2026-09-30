"""A non-power witness for the weakened42 binary power-geometry source.

Main coordinates and the weak auxiliary CRT are exact integers. The final
auxiliary Pell values have a parametric construction, not a materialized tuple.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import gcd
from pathlib import Path
import sympy as sp
import pell_kernel_power_two43 as geometry
import native_controller_three_selector_53 as execution


SCHEDULE = [(name, op, 'ic2' if left == 'ic22' else left,
             'ic2' if right == 'ic22' else right)
            for name, op, left, right in geometry.SCHEDULE if name != 'ic22']
EQUALITIES = [('ic2' if left == 'ic22' else left,
               'ic2' if right == 'ic22' else right)
              for left, right in geometry.EQUALITIES]


def source_check():
    z = {name: sp.Symbol(name) for name in geometry.NAMES}
    env = execution.execute(SCHEDULE, z)
    sources = geometry.sources(z)
    delta = z['a']**2 + 4*z['a'] + 3
    sources[8] = z['i']*z['c']**2 - delta*(z['f']**2-1)
    u = z['j']*z['c']-(2*z['r']+1)
    correction = sources[8]*(u*u-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(EQUALITIES, sources)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE) == 42 and counts['*'] == 24
    assert counts['+']+counts['-'] == 18 and len(sources) == 11
    return dict(operations=42, multiplications=24, additions_subtractions=18,
                equations=11, positive_parameters=['q'],
                positive_auxiliaries=geometry.NAMES[1:],
                instructions=[list(row) for row in SCHEDULE], sources=records,
                change='Replace (i*c^2)^2 by i*c^2; retain the free r1=q comparison')


def integer_record(value):
    assert value > 0
    payload = value.to_bytes((value.bit_length()+7)//8, 'big')
    return dict(bits=value.bit_length(), unsigned_big_endian_sha256=hashlib.sha256(payload).hexdigest())


def counterexample():
    q = X = Y = 5
    r, J, a, A, P, p, n = 4, 9, 30, 32, 251, 14587, 9755
    delta, modulus, E = A*A-1, 4*a+3, X*Y
    d, c = geometry.pell(A, p)
    first_chi, k = geometry.pell(P, n)
    eta, zeta = c-Y*k, (Y+1)*k-c
    assert eta > 0 and zeta > 0
    assert pow(2, p, modulus) == X and n % E == r+1
    assert (k-r-1) % E == 0 and (d-X-a*c) % modulus == 0
    assert first_chi % 2 == 1 and gcd(p, c) == 1
    values = dict(q=q, r=r, w=1, s=1, a=a, c=c, d=d, k=k,
                  tau=(first_chi-1)//2, eta=eta, zeta=zeta,
                  h=(k-r-1)//E, ga=(d-X-a*c)//modulus)
    assert min(values.values()) > 0
    # Every equality through the main Pell norm is checked from the literal DAG.
    env = execution.execute(SCHEDULE[:29], values)
    for left, right in EQUALITIES[:8]:
        assert env[left] == env[right], (left, right)
    assert c*10000 > 55828*k and c*10000 < 55829*k

    # Prescribed weak auxiliary extension, with m=2p.
    f = 2*d*d-1
    R = 2*delta*c*d
    i = 4*delta*delta*d*d
    assert i*c*c == R*R == delta*(f*f-1)
    sigma = (-1)**((p-1)//2)
    t = ((-sigma*J-p)*pow(4*p, -1, c)) % c
    if (-1)**t != -sigma:
        t += c
    auxiliary_index = p+4*p*t
    assert auxiliary_index % 2 == 1 and auxiliary_index >= 3
    assert sigma*auxiliary_index % c == (-J) % c
    assert sigma*((-1)**t) == -1
    assert auxiliary_index % 4 == p % 4
    assert gcd(c, d) == 1 and c % 2 == 1
    assert R > f > 2*c > J and c > 2*p
    assert (R*R + delta) % f == 0 and R % c == 0
    assert pow(2, 7, modulus) == X and pow(2, 20, modulus) == 1
    assert p == 7+20*729 and n == 5+25*390
    return dict(parameters=dict(q=q, r=r, J=J, X=X, Y=Y, a=a, A=A,
                first_parameter=P, main_index=p, first_index=n,
                discriminant=delta, exponent_modulus=modulus),
                exact_main_equalities=8, ratio_interval=[55828, 55829, 10000],
                gcd_main_index_c=1,
                main_coordinates={name: integer_record(v) for name, v in values.items()},
                weak_auxiliary={name: integer_record(v) for name, v in
                                dict(f=f, R=R, i=i, crt_t=t, auxiliary_index=auxiliary_index).items()},
                crt=dict(sigma=sigma, t_parity=t % 2,
                         normalized_u_mod_c='-J', normalized_u_mod_f='-c'),
                final_coordinates='y_aux=psi_R(auxiliary_index); U=chi_R(auxiliary_index)/R; j=(U+J)/c; o=(U+c)/f',
                final_coordinate_materialization=False,
                conclusion='All eleven weakened equations have positive witnesses at q=5, which is not a power of two')


def verify():
    return dict(status='PASS_WEAK42_POWER_GEOMETRY_COUNTEREXAMPLE', source=source_check(),
                counterexample=counterexample(),
                scope='Refutes only the single-product weakening of binary power geometry; complete43 remains valid and the older complete75 candidate remains open',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'], operations=result['source']['operations'],
                         parameters=result['counterexample']['parameters'],
                         final_auxiliaries_materialized=False, scope=result['scope']), indent=2))
