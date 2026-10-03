#!/usr/bin/env python3
"""Exact checks for the L-convex/colored-partition comparison.

Only the Python standard library is needed. The computations are checks, not
substitutes for the proofs in the accompanying article.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path


def divide_square(coeffs: list[int], step: int) -> list[int]:
    """Divide a truncated integer series by (1-q**step)**2."""
    out = coeffs.copy()
    for _ in range(2):
        for j in range(step, len(out)):
            out[j] += out[j-step]
    return out


def normalized_family(N: int, y0: int, y1: int, collect: bool=False):
    """Return slope and C(q), C(q^2) for y[n+1]=2y[n]-(1-q^n)^2 y[n-1]."""
    prev2 = [y0] + [0]*N
    prev = [y1*(j+1) for j in range(N+1)]
    C1 = [y0] + [0]*N
    C2 = [y0] + [0]*N
    def add_terms(b: list[int], n: int) -> None:
        for j in range(N-n+1):
            C1[j+n] += b[j]
        if 2*n <= N:
            for j in range(N-2*n+1):
                C2[j+2*n] += b[j]
    if collect:
        add_terms(prev, 1)
    for n in range(2, N+2):
        rhs = [2*x-y for x,y in zip(prev,prev2)]
        now = divide_square(rhs,n)
        if collect and n <= N:
            add_terms(now,n)
        prev2,prev = prev,now
    slope = [x-y for x,y in zip(prev,prev2)]
    return slope,C1,C2


def colored_partitions(N: int) -> list[int]:
    p = [1]+[0]*N
    for j in range(1,N+1):
        colors = 4 - 2*(j%2==0) + (j%4==0)
        for _ in range(colors):
            for n in range(j,N+1):
                p[n] += p[n-j]
    return p


def polynomial_times_series(poly: list[int], series: list[int]) -> list[int]:
    """Multiply by a polynomial, truncating to the input series length."""
    result = [0] * len(series)
    for degree, coefficient in enumerate(poly):
        if coefficient:
            for n in range(degree, len(series)):
                result[n] += coefficient * series[n-degree]
    return result


def polynomial_product(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a*b
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax',type=int,default=2000)
    ap.add_argument('--out',type=Path,default=Path('checks'))
    args = ap.parse_args()
    if args.nmax < 36:
        ap.error('--nmax must be at least 36')
    N = args.nmax
    args.out.mkdir(parents=True,exist_ok=True)
    Lh,C1,C2 = normalized_family(N,1,1,True)
    E,_,_ = normalized_family(N,-1,0)
    p = colored_partitions(N)
    a = [x-y+(i==0) for i,(x,y) in enumerate(zip(C1,C2))]
    j = [p[n]-2*(p[n-1] if n>=1 else 0)+(p[n-2] if n>=2 else 0) for n in range(N+1)]
    prefix = [1,1,2,6,15,35,76,156,310,590,1098,1984,3515,6094,
              10398,17434,28837,47038,75820,120794,190479,297365,
              460056,705576,1073473,1620680,2429352,3616580,
              5349359,7863564,11491946,16700534,24140606,34716813,
              49682700,70766326,100343410]
    assert a[:len(prefix)] == prefix, 'OEIS prefix mismatch'
    assert all(p[n]-2*Lh[n] == E[n] for n in range(N+1))
    assert all(p[n]-4*a[n]+6*(n==0) == E[n]+2*C2[n] for n in range(N+1))
    assert all(0 <= E[n] <= j[n] for n in range(N+1))
    assert all(C2[n] <= j[n]+(n==1)+2*(n==2) for n in range(N+1))
    assert all(0 <= p[n]-4*a[n] <= 3*j[n] for n in range(3,N+1))
    # Check the third finite-cut identity without division by Q_3.
    C3 = [2*x-y for x,y in zip(C2,polynomial_times_series([1,-2,1],C1))]
    C3[1] -= 1
    C4 = [2*x-y for x,y in zip(C3,polynomial_times_series([1,0,-2,0,1],C2))]
    C4[2] -= 1
    h3 = [1,4,0,0,-1]
    Q3 = [4,4,2,0,-2]
    U3_plus_P3 = [3,2,3,0,-1]
    E3 = [x-y for x,y in zip(polynomial_times_series(h3,p),
                             polynomial_times_series(Q3,Lh))]
    assert all(v >= 0 for v in C3+C4+E3), 'third-cut positivity failed'
    Q3sq = polynomial_product(Q3,Q3)
    left = polynomial_times_series(Q3sq,a)
    right = polynomial_times_series(polynomial_product(h3,h3),p)
    for term in (polynomial_times_series(h3,E3),
                 polynomial_times_series(Q3,C4)):
        right = [x-y for x,y in zip(right,term)]
    for n,value in enumerate(Q3sq):
        right[n] += 2*value
    for n,value in enumerate(polynomial_product(U3_plus_P3,Q3)):
        right[n] -= value
    assert left == right, 'polynomial-cleared third-cut identity failed'
    # Independently read selected terms from the OEIS b-file, not inferred.
    anchors = {50:8997185064,100:2567462560505766,
               200:196484348482948620602584,
               500:1643781053049901500607437276388342882780}
    for n,value in anchors.items():
        if n <= N:
            assert a[n] == value, ('OEIS b-file anchor mismatch',n)
    A = 13*math.pi**2/24
    B = 2*math.sqrt(A)
    c = 13*math.sqrt(2)/768
    d = B/12+3/B
    rows = []
    for n in [50,100,200,500,1000,2000,5000,10000]:
        if n>N: continue
        lead = c*math.exp(B*math.sqrt(n))/n**1.5
        rows.append(dict(n=n,ratio_leading=a[n]/lead,
                         scaled_first=(a[n]/lead-1)*math.sqrt(n),
                         ratio_two_term=a[n]/(lead*(1-d/math.sqrt(n))),
                         normalized_deficit=n*(p[n]-4*a[n])/p[n],
                         upper_bound=3*n*j[n]/p[n]))
    with (args.out/'numerical_table.csv').open('w',newline='') as f:
        fields = ['n','ratio_leading','scaled_first','ratio_two_term',
                  'normalized_deficit','upper_bound']
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)
    with (args.out/'coefficients.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['n','a_n','p_n','p_n_minus_4a_n','j_n'])
        for n in range(N+1): writer.writerow([n,a[n],p[n],p[n]-4*a[n],j[n]])
    report={'nmax':N,'exact_assertions':'all passed','oeis_prefix_terms':len(prefix),
            'oeis_bfile_anchors_checked':[n for n in anchors if n<=N],
            'A':A,'B':B,'c':c,'first_correction_magnitude':d,
            'checks':['normalization against OEIS','slope product identity',
                      'exact positive decomposition','E <= (1-q)^2 R',
                      'C(q^2) <= (1-q)^2 R + q + 2q^2',
                      'coefficient squeeze for every 3 <= n <= nmax',
                      'third-cut positive tails E_3, C_3, C_4',
                      'third-cut identity after multiplying by Q_3^2']}
    (args.out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    for row in rows: print(row)

if __name__=='__main__':
    main()
