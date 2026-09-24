"""Same-count odd-r auxiliary signs; exact arithmetic, not a new bound."""

from collections import Counter
import json
from pathlib import Path
import sympy as sp

import round42_1980_implicit_history_bound as previous
from explore_fixed_radix_pell_kernel import evaluate
from round37_1980_base_two_pell_regression import pell_power


def verify():
    rows = []
    for row in previous.SCHEDULE:
        if row[0] == 'H17':
            row = ('H17', '-', 'jc', 'tr1')
        elif row[0] == 'aux_u_rhs':
            row = ('aux_u_rhs', '-', 'of', 'c')
        rows.append(row)
    env = evaluate(rows, previous.SYM)
    assert len(rows) == 82
    assert Counter(row[1] for row in rows) == {'*':45, '+':29, '-':8}
    z = previous.SYM
    auxu = z['j']*z['c']-(2*z['r']+1)
    K = (z['a']**2+4*z['a']+3)*(z['f']**2-1)
    source = previous.source_residuals()
    source[18] = K*(auxu**2-z['y_aux']**2)-(1-z['y_aux']**2)
    source[19] = auxu+z['c']-z['o']*z['f']
    correction = source[17]*(auxu**2-z['y_aux']**2)
    for index, ((left,right), residual) in enumerate(zip(previous.EQUALITIES,source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 18 else 0
        assert (sp.expand(actual-residual-adjustment) == 0
                or (adjustment == 0 and sp.expand(actual+residual) == 0)), index

    cases = []
    for A,J in [(2,3),(2,7),(3,3),(4,3),(5,3)]:
        d,c = pell_power(A,J)
        D,m = A*A-1,2*c*J
        f,psim = pell_power(A,m)
        R = D*psim
        i,rem = divmod(R,c*c)
        assert rem == 0 and i > 0 and R*R == D*(f*f-1)
        chi,y = pell_power(R,J)
        u,rem = divmod(chi,R)
        assert rem == 0 and u > c and u > J
        j,remj = divmod(u+J,c)
        o,remo = divmod(u+c,f)
        assert remj == remo == 0 and j > 0 and o > 0
        assert u == j*c-J == o*f-c
        assert R*R*(u*u-y*y) == 1-y*y
        cases.append({'A':A, 'J':J, 'r':(J-1)//2, 'u_bits':u.bit_length(),
                      'positive_integral_auxiliaries':True})
    return {
        'status':'SAME_COUNT_ODD_R_KERNEL_PASS_NO_OPERATION_REDUCTION',
        'operations':82,
        'multiplications':45,
        'additions_subtractions':37,
        'retained_kernel_operations':43,
        'exact_source_residuals':20,
        'new_congruences':['u=j*c-J', 'u=o*f-c'],
        'auxiliary_only_cases':cases,
        'scope':'Odd-r positive auxiliary construction and modified exact arithmetic only. The current even-r history compiler is not replaced. No smaller universal certificate is claimed.',
        'proof':'../1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md',
    }


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['status'], len(receipt['auxiliary_only_cases']), 'exact auxiliary cases')
