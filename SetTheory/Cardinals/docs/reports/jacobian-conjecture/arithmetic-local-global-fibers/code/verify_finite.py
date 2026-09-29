#!/usr/bin/env python3
"""Dependency-free exact checks for Arithmetic Local--Global Dichotomies.

The theorem for every p-adic precision uses the inverse-ball lemma in the
article, not extrapolation from the finite tests in this file.
"""
from __future__ import annotations
import argparse
import itertools
import json
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
from pathlib import Path

Triple = tuple[int, int, int]

def F(x, y, z):
    u = 1 + x*y
    h = u*u*z + y*y*(1 + 3*u)
    return (u*h, y + 3*x*h, x*(5 - 3*u - x*x*z))

def F_expanded(x: int, y: int, z: int) -> Triple:
    return (z + 3*x*y*z + 3*x*x*y*y*z + x**3*y**3*z
            + 4*y*y + 7*x*y**3 + 3*x*x*y**4,
            y + 3*x*z + 6*x*x*y*z + 3*x**3*y*y*z
            + 12*x*y*y + 9*x*x*y**3,
            2*x - 3*x*x*y - x**3*z)

def jacobian(x: int, y: int, z: int):
    """Derivatives from product rules for the factored definition."""
    u = 1+x*y
    h = u*u*z+y*y*(1+3*u)
    hx = 2*u*y*z+3*y**3
    hy = 2*u*x*z+2*y*(1+3*u)+3*x*y*y
    hz = u*u
    return ((y*h+u*hx, x*h+u*hy, u*hz),
            (3*h+3*x*hx, 1+3*x*hy, 3*x*hz),
            (2-6*x*y-3*x*x*z, -3*x*x, -x**3))

def counts_mod(m: int, expanded: bool = False) -> Counter:
    if m < 1:
        raise ValueError('Modulus must be positive')
    f = F_expanded if expanded else F
    return Counter(tuple(v % m for v in f(*a))
                   for a in itertools.product(range(m), repeat=3))

def histogram(counts: Counter, m: int) -> dict[int, int]:
    h = Counter(counts.values())
    h[0] = m**3-len(counts)
    return dict(sorted(h.items()))

def inverse_family(n: int):
    if n < 2:
        raise ValueError('The family is indexed by n >= 2')
    roots = (0, n, 1-n)
    ds = (-n*(n-1), n*(2*n-1), (n-1)*(2*n-1))
    points = [(Fraction(1,d), t-d, 5*d*d-3*t*d-2*d**3)
              for t,d in zip(roots,ds)]
    return roots, ds, points

def prime_powers(m: int) -> list[tuple[int,int]]:
    if m < 1:
        raise ValueError('Modulus must be positive')
    result = []
    p = 2
    while p*p <= m:
        if m % p == 0:
            q = 1
            while m % p == 0:
                q *= p
                m //= p
            result.append((p,q))
        p += 1
    if m > 1:
        result.append((m,m))
    return result

def crt_pairwise(residues: list[int], moduli: list[int]) -> int:
    result, modulus = 0, 1
    for r,m in zip(residues,moduli):
        result += modulus * (((r-result)*pow(modulus,-1,m)) % m)
        modulus *= m
        result %= modulus
    return result

def congruence_preimage(n: int, modulus: int) -> Triple:
    """Construct F(a) == (0,-2n(n-1),2) mod modulus, using local branches."""
    if modulus < 1:
        raise ValueError('Modulus must be positive')
    _, ds, pts = inverse_family(n)
    local = []
    mods = []
    for p,power in prime_powers(modulus):
        idx = next(i for i,d in enumerate(ds) if d % p != 0)
        point = [Fraction(v) for v in pts[idx]]
        local.append(tuple(v.numerator*pow(v.denominator,-1,power) % power
                           for v in point))
        mods.append(power)
    return tuple(crt_pairwise([v[j] for v in local], mods) for j in range(3))

def main(output: Path | None = None) -> dict:
    result = {'scope': 'Exact finite certificates; all-prime and all-precision proofs are in the article.'}
    # Test completely independent expanded and factored polynomial evaluators.
    for a in itertools.product(range(-3,4),repeat=3):
        assert F(*a) == F_expanded(*a)
    result['expanded_evaluator_checks'] = 7**3

    # All three family branches, using exact rational arithmetic.
    for n in range(2,101):
        roots,ds,pts = inverse_family(n)
        target=(0,-2*n*(n-1),2)
        assert all(F(*a)==target for a in pts)
        assert all(abs(d)>1 for d in ds)
        assert gcd(gcd(*ds[:2]),ds[2])==1
        assert len(set(pts))==3
    result['family_indices_checked'] = [2,100]
    result['family_n2'] = [[str(c) for c in pt] for pt in inverse_family(2)[2]]

    # The residue-8 table, and an independently structured ball-image check.
    direct8=counts_mod(8)
    assert direct8==counts_mod(8,expanded=True)
    actual={a:direct8[a]//2 for a in itertools.product(range(8),repeat=3)}
    assert all(v%2==0 for v in direct8.values())
    balls=Counter()
    ball_details=[]
    for a in itertools.product(range(4), repeat=3):
        J=jacobian(*a)
        f=F(*a)
        image={tuple((f[i]+4*sum(J[i][j]*h[j] for j in range(3)))%8
                     for i in range(3)) for h in itertools.product(range(2),repeat=3)}
        assert len(image)==4
        for b in image:
            balls[b]+=1
        ball_details.append({'source_mod4':a,'image_mod8':sorted(image)})
    assert all(actual[a]==balls[a] for a in actual)
    parity=defaultdict(Counter)
    for b,j in actual.items():
        parity[tuple(c%2 for c in b)][j]+=1
    result['dyadic_parity_table']=[{'target_parity':k,'j0_j1_j2_j3':[parity[k][j] for j in range(4)]}
                                    for k in sorted(parity)]
    assert [sum(parity[k][j] for k in parity) for j in range(4)]==[336,112,48,16]
    result['dyadic_actual_counts_mod8']=[336,112,48,16]
    result['dyadic_ball_images']=ball_details
    result['dyadic_congruence_histograms']={}
    for m in (2,4,8,16,32):
        c=direct8 if m==8 else counts_mod(m)
        h=histogram(c,m)
        result['dyadic_congruence_histograms'][m]=h
        if m>=8:
            assert h=={0:21*m**3//32,2:7*m**3//32,4:3*m**3//32,6:m**3//32}
            # Stronger than a histogram: every target's count is as predicted.
            assert all(c[b]==2*actual[tuple(x%8 for x in b)]
                       for b in itertools.product(range(m),repeat=3))
    groups=defaultdict(list)
    for b,j in actual.items():
        groups[tuple(c%4 for c in b)].append((b,j))
    witness=None
    for group in groups.values():
        missing=next((b for b,j in group if j==0),None)
        present=next((b for b,j in group if j>0),None)
        if missing is not None and present is not None:
            witness={'omitted_target':missing,'present_target':present,
                     'present_fiber_size':actual[present]}
            break
    assert witness is not None
    result['mod8_necessary_for_image_witness']=witness

    # Prime field laws (known formulas, newly reproduced checks).
    result['odd_prime_histograms']={}
    for p in (3,5,7,11,13,17,19,23,29,31):
        h=histogram(counts_mod(p),p)
        expected=({0:p*p*(p-1)//3,1:p*p*(p+1)//2,3:p*p*(p-1)//6}
                  if p==3 else
                  {0:(p-1)*(p*p+2)//3,1:(p**3+p*p-2*p+2)//2,3:(p-1)*(p*p+2)//6})
        assert h==expected, (p,h,expected)
        result['odd_prime_histograms'][p]=h
    result['odd_prime_power_histograms']={}
    for p,e in ((3,2),(3,3),(5,2)):
        m=p**e
        c=counts_mod(m)
        c0=counts_mod(p)
        assert all(c[b]==c0[tuple(x%p for x in b)]
                   for b in itertools.product(range(m),repeat=3))
        result['odd_prime_power_histograms'][m]=histogram(c,m)

    result['CRT_examples']=[]
    for n,m in ((2,21600),(3,10800),(17,360360),(42,54000)):
        a=congruence_preimage(n,m)
        b=(0,-2*n*(n-1),2)
        assert tuple(c%m for c in F(*a))==tuple(c%m for c in b)
        result['CRT_examples'].append({'n':n,'modulus':m,'source':a,'target':b})
    result['status']='PASS'
    if output:
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PASS: expanded/factored evaluator agreement on 343 integer points')
    print('PASS: all three split-family branches for n=2,...,100 (exact fractions)')
    print('PASS: direct and 64-ball dyadic counts agree pointwise modulo 8')
    print('Actual Z_2 fiber counts in 512 target residue classes:',result['dyadic_actual_counts_mod8'])
    print('Target parity | counts j=0,1,2,3')
    for row in result['dyadic_parity_table']:
        print(row['target_parity'], row['j0_j1_j2_j3'])
    print('PASS: pointwise stabilization checked at moduli 8,16,32')
    print('Minimal image modulus witness:',witness)
    print('PASS: known odd-prime formulas through p=31, and prime-power checks at 9,27,25')
    print('PASS: CRT constructions:',result['CRT_examples'])
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Write detailed exact JSON certificate')
    args=parser.parse_args()
    main(args.output)
