#!/usr/bin/env python3
"""Replay the exact finite certificates. Uses only the Python standard library.

This checks arithmetic, the finite graph, and consistency of the supplied
profile. It does NOT prove that the profile enumerates all polyominoes and
it is NOT a formal proof of the analytic theorems in the article.
"""
from __future__ import annotations
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
from bui_model import NAMES, TERMS, load_profiles, horner, jacobian, matvec

ROOT = Path(__file__).resolve().parents[1]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)

def conv(a: list, b: list, length: int) -> list:
    out = [0] * length
    for i, x in enumerate(a[:length]):
        for j, y in enumerate(b[:length-i]):
            out[i+j] += x*y
    return out

def polynomial_map(coeffs: list[list[int]], length: int) -> list[list[int]]:
    answer = []
    for row in TERMS:
        out = [0]*length
        for degree, indices in row:
            term = [0]*degree + [1]
            for j in indices:
                term = conv(term, coeffs[j], length)
            for k, value in enumerate(term[:length]):
                out[k] += value
        answer.append(out)
    return answer

def directional_derivative(t: Q, a: list[Q], w: list[int]) -> list[Q]:
    """Independent product-rule implementation via dual-number arithmetic."""
    answer = []
    for row in TERMS:
        coefficient = Q(0)
        for power, indices in row:
            constant, linear = t**power, Q(0)
            for j in indices:
                constant, linear = constant*a[j], linear*a[j]+constant*w[j]
            coefficient += linear
        answer.append(coefficient)
    return answer

def strongly_connected(matrix: list[list]) -> bool:
    n = len(matrix)
    for start in range(n):
        seen, stack = {start}, [start]
        while stack:
            i = stack.pop()
            for j, value in enumerate(matrix[i]):
                if value > 0 and j not in seen:
                    seen.add(j)
                    stack.append(j)
        if len(seen) != n:
            return False
    return True

def matmul(a: list[list], b: list[list]) -> list[list]:
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def exact_bui() -> dict:
    obj = json.loads((ROOT/'data/bui_spectral_certificate.json').read_text())
    require(obj['variable_order'] == NAMES, 'Variable order mismatch')
    require(obj['prefix_size'] == 18, 'Wrong prefix size')
    t = Q(obj['evaluation_numerator'], obj['evaluation_denominator'])
    require(t == Q(10000,43149), 'Wrong evaluation point')
    w = obj['positive_integer_vector']
    require(len(w) == 17 and all(isinstance(x,int) and x > 0 for x in w),
            'Witness must contain 17 positive integers')
    factor = Q(obj['certified_factor_numerator'],obj['certified_factor_denominator'])
    require(factor == Q(1000001,1000000), 'Wrong certified factor')
    profiles = load_profiles(ROOT/'data/profiles_18.csv')
    require(all(x >= 0 for row in profiles for x in row), 'Negative input count')
    a = [horner(p,t) for p in profiles]
    require(all(x > 0 for x in a), 'Profile values must be positive')
    J = jacobian(t,a)
    image = matvec(J,w)
    require(image == directional_derivative(t,a,w), 'Derivative cross-check failed')
    require(all(x >= factor*y for x,y in zip(image,w)), 'Spectral certificate failed')
    require(strongly_connected(J), 'Dependency graph is not strongly connected')
    linear = jacobian(Q(0),[Q(0)]*17)
    power = [[int(i==j) for j in range(17)] for i in range(17)]
    nilpotency_index = None
    for k in range(1,18):
        power = matmul(power,linear)
        if all(x == 0 for row in power for x in row):
            nilpotency_index = k
            break
    require(nilpotency_index is not None, 'Constant linear part not nilpotent')
    fmap = polynomial_map(profiles, 19)
    defects = [[x-y for x,y in zip(f,p)] for f,p in zip(fmap,profiles)]
    require(all(x >= 0 for row in defects for x in row), 'Negative profile defect')
    partitions = [(3,4,6),(4,2,7),(5,1,9),(8,15,13),(10,14,12)]
    for i,j,k in partitions:
        require(all(x == y+z for x,y,z in zip(profiles[i],profiles[j],profiles[k])),
                'Profile partition identity failed')
    # The c row t+t*e forces a nonzero term beyond every nonzero top e coefficient.
    require(TERMS[0] == [(1,()),(1,(2,))], 'Forcing row changed')
    require(profiles[2][18] == 1616425239, 'Unexpected e_18')
    margins = [(x-factor*y) for x,y in zip(image,w)]
    ratios = [x/Q(y)-1 for x,y in zip(image,w)]
    with localcontext() as ctx:
        ctx.prec=25
        min_ratio=min(ratios)
        approximate=str(Decimal(min_ratio.numerator)/Decimal(min_ratio.denominator))
    return {
        'status':'PASS', 'monomials':sum(map(len,TERMS)),
        'positive_coordinates':17, 'nilpotency_index':nilpotency_index,
        'spectral_factor':'1000001/1000000',
        'growth_wall':'43149/10000', 'evaluation':'10000/43149',
        'minimum_ratio_minus_one_decimal_display':approximate,
        'all_17_residuals_strictly_positive':all(x>0 for x in margins),
        'profile_partition_checks':5*19,
        'profile_defect_checks':17*19,
        'trust_boundary':'Input marked counts are inherited, not re-enumerated.'
    }

def scalar_polynomial(N: int, t: Q) -> Q:
    return (1-3*t)**2-4*t**(N+1)*((N-1)-(N-2)*t)

def scalar_root_bracket(N: int, bits: int=260) -> tuple[Q,Q]:
    if N < 3 or bits < 8:
        raise ValueError('N >= 3 and bits >= 8 required')
    lo, hi = Q(1,4), Q(1,3)
    require(scalar_polynomial(N,lo)>0 and scalar_polynomial(N,hi)<0,
            'Initial bracket has wrong signs')
    for _ in range(bits):
        mid = (lo+hi)/2
        value = scalar_polynomial(N,mid)
        if value == 0:
            return mid,mid
        if value>0:
            lo=mid
        else:
            hi=mid
    require(scalar_polynomial(N,lo)>=0 and scalar_polynomial(N,hi)<=0,
            'Final bracket has wrong signs')
    return lo,hi

def dec(q: Q) -> Decimal:
    return Decimal(q.numerator)/Decimal(q.denominator)

def exact_scalar() -> tuple[list[dict],str]:
    entries=[]
    tex=[r'\begin{tabular}{@{}rrrr@{}}',r'\toprule',
         r'$N$ & $\rho_N$ (rounded) & $\rho_* -\rho_N$ & ratio to leading term\\',
         r'\midrule']
    for N in [4,8,16,32,64,128]:
        lo,hi=scalar_root_bracket(N)
        # Directly check the unmultiplied discriminant identity at independent rational points.
        for t in [Q(1,5),Q(2,7),Q(1,3)]:
            D=sum(Q(n-2)*t**n for n in range(3,N+1))
            require(scalar_polynomial(N,t)==(1-t)**2*(1-4*t+4*D),
                    'Scalar discriminant identity failed')
        with localcontext() as ctx:
            ctx.prec=75
            midpoint=dec((lo+hi)/2)
            gap=Decimal(1)/3-midpoint
            leading=Decimal(4)/9*dec(Q(2*N-1,4*3**N)).sqrt()
            ratio=gap/leading
            entry={'N':N,'root_lower':str(lo),'root_upper':str(hi),
                   'bracket_width':str(hi-lo),'root_decimal':str(midpoint),
                   'gap_decimal':str(gap),'gap_over_leading_decimal':str(ratio)}
            entries.append(entry)
            mantissa, exponent = f'{gap:.5E}'.split('E')
            scientific = mantissa + r'\times10^{' + str(int(exponent)) + '}'
            tex.append(f'{N} & {midpoint:.12f} & ${scientific}$ & {ratio:.9f} \\\\')
    tex += [r'\bottomrule',r'\end{tabular}']
    return entries, '\n'.join(tex)+'\n'

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Write reproduced outputs and TeX tables')
    args=parser.parse_args()
    bui=exact_bui()
    scalar,table=exact_scalar()
    report={'bui':bui,'scalar':{'status':'PASS','number_of_brackets':len(scalar),
                              'bits_per_bracket':260,'entries':scalar},
            'analytic_theorems':'Not established by this finite checker; see article proofs.'}
    print('PASS: 17 exact Bui inequalities and independent directional derivative check')
    print('PASS: strong connectivity, properness, 5 partition identities, all prefix defects')
    print('PASS: 6 exact scalar brackets (260 bisections each) and 18 identity evaluations')
    print('Certified fixed-map prefix growth wall: 4.3149 (NOT a polyomino lower bound)')
    print('Input size-18 profile was not re-enumerated. No Lean verification is claimed.')
    if args.write:
        (ROOT/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n')
        (ROOT/'data/scalar_table.tex').write_text(table)
        obj=json.loads((ROOT/'data/bui_spectral_certificate.json').read_text())
        lines=[r'\begin{tabular}{@{}lr@{}}',r'\toprule',r'coordinate & $w_i$\\',r'\midrule']
        lines += [f'${name}$ & {value:,} \\\\' for name,value in zip(NAMES,obj['positive_integer_vector'])]
        lines += [r'\bottomrule',r'\end{tabular}']
        (ROOT/'data/witness_table.tex').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':
    main()
