#!/usr/bin/env python3
"""Exact 44-operation general-scale ternary kernel, both index parities."""
from pathlib import Path
import json
import sympy as sp

import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
from round37_1980_base_two_pell_regression import pell_power
import explore_base_three_positive_kernel as original

PARAMETERS = ['D0', 'r']
AUXILIARIES = [name for name in original.CORE_NAMES if name != 'r'] + ['u']
SYM = {name: sp.Symbol(name) for name in PARAMETERS + AUXILIARIES}
SCHEDULE = []
for old in original.CORE:
    row = tuple('D0' if value == 'n2' else value for value in old)
    if row[0] == 'aux_u_rhs':
        row = ('aux_u_rhs', '+', 'c2', 'of')
    elif row[0] == 'H17':
        SCHEDULE.append(('J_square', '*', 'tr1', 'tr1'))
        row = ('H17', '+', 'J_square', 'jc')
    elif row[0] == 'H2':
        row = ('H2', '*', 'u', 'u')
    SCHEDULE.append(row)
EQUALITIES = original.EQUALITIES[1:-1] + [('H2', 'H17'), ('H2', 'aux_u_rhs')]


def source_residuals():
    z = SYM
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = [z[n] for n in original.CORE_NAMES]
    u, scale = z['u'], z['D0']
    U, Y = w*scale, s*scale
    Q, D = U*Y**2, a*a+6*a+8
    return [
        Q*(Q+1)*k*k-tau*(tau+1),
        c-Y*k-eta, k-eta-zeta, k-r-1-h*U*Y,
        a-Y*(U+1), d-U-a*c-ga*(6*a+8),
        d*d-D*c*c-1, (i*c*c)**2-D*(f*f-1),
        D*(f*f-1)*(u*u-y*y)-(1-y*y),
        u*u-(2*r+1)**2-j*c, u*u-c*c-o*f,
    ]


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    correction = source[7]*(SYM['u']**2-SYM['y_aux']**2)
    records = []
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 8 else sp.Integer(0)
        assert sp.expand(actual-residual-adjustment) == 0, index
        records.append(dict(index=index, equality=[left,right],
                            source=sp.sstr(sp.expand(residual)),
                            actual=sp.sstr(actual), correction=sp.sstr(sp.expand(adjustment))))
    primitives, counts = verify_primitives(SCHEDULE, env)
    assert len(SCHEDULE) == len(primitives) == 44
    assert counts == {'+':18, '*':26}
    assert len(records) == len(source) == len(EQUALITIES) == 11
    assert len(AUXILIARIES) == 17
    used = {value for row in SCHEDULE for value in row[2:]}
    used |= {value for pair in EQUALITIES for value in pair}
    assert set(SYM) <= used
    assert all(p.free_symbols <= set(SYM.values()) for p in source)
    return dict(arithmetic_status='PASS', operations=44,
                primitive_histogram=counts, histogram=histogram,
                parameters=PARAMETERS, positive_auxiliaries=AUXILIARIES,
                equations=11, primitive_instructions=primitives,
                equalities=EQUALITIES, residuals=records)


def preliminary_regression():
    cases = 0
    for scale in range(81,301):
        for r in range(27,2*scale):
            if scale >= r*r:
                continue
            assert scale*scale > r+1
            assert scale*(scale+1) > 2*r+1
            assert 12*r < scale*(scale+1)
            assert r+2 >= 29 and 2*r+1 < 2*(r+2)
            cases += 1
    for p in range(7,101):
        c_lower = 3**(p-1)
        assert c_lower > 4*p*p
        for J in range(1,2*p):
            assert 0 < p*p < c_lower and 0 < J*J < c_lower
            assert ((p*p-J*J) % c_lower == 0) == (p == J)
    return dict(preliminary_cases=cases,
                square_index_cases=sum(2*p-1 for p in range(7,101)),
                minimum_scale=81, minimum_r=27)


def auxiliary_regression():
    rows = []
    for A,r in [(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)]:
        J = 2*r+1
        _, c = pell_power(A,J)
        D, m = A*A-1, 2*c*J
        f, psi_m = pell_power(A,m)
        R = D*psi_m
        i, rem = divmod(R,c*c)
        assert rem == 0 and i > 0 and R*R == D*(f*f-1)
        chi, y = pell_power(R,J)
        u, rem = divmod(chi,R)
        assert rem == 0 and u > c > J
        assert (u-(-1)**r*c) % f == 0
        assert (u-(-1)**r*J) % c == 0
        j, rem_j = divmod(u*u-J*J,c)
        o, rem_o = divmod(u*u-c*c,f)
        assert rem_j == rem_o == 0 and j > 0 and o > 0
        assert u*u == J*J+j*c == c*c+o*f
        assert R*R*(u*u-y*y) == 1-y*y
        rows.append(dict(A=A,r=r,J=J,parity=r%2,
                         u_bits=u.bit_length(),j_bits=j.bit_length(),o_bits=o.bit_length(),
                         positive_integral_auxiliaries=True))
    return rows


def verify():
    result = verify_certificate()
    result['preliminary_regression'] = preliminary_regression()
    result['auxiliary_only_cases'] = auxiliary_regression()
    result['proof'] = '../1980/EXPLORATION_PARITY_FREE_PELL_KERNEL.md'
    result['scope'] = ('Conditional 44-operation general-scale ternary kernel for either parity. '
                       'Scale/index construction, bounds, masks and computation interfaces are excluded. '
                       'Small exact auxiliary tuples check the squared congruences only; no full huge kernel tuple is materialized.')
    return result


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['arithmetic_status'],result['operations'],result['primitive_histogram'],result['equations'])
    print(result['preliminary_regression'])
    print(len(result['auxiliary_only_cases']), 'exact auxiliary tuples, both parities')
