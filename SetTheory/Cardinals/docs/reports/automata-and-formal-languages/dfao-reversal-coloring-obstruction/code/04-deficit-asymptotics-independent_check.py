#!/usr/bin/env python3
"""Independent reconstruction of the finite certificate. No producer imports.
Permutation orders use unrestricted dynamic programming, rather than partitions.
Complete-bipartite colorings use inclusion-exclusion, rather than the closed form.
"""
from __future__ import annotations
import itertools, json, math
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def check(ok, message):
    if not ok:
        raise RuntimeError(message)

def onto(n,j):
    return sum((-1)**t*math.comb(j,t)*(j-t)**n for t in range(j+1))

def bipartite(a,b,k=3):
    return sum(math.comb(k,j)*onto(a,j)*(k-j)**b for j in range(1,k))

def main():
    cert=json.loads((ROOT/'results/finite_certificate.json').read_text())
    maxn=max(row['n'] for row in cert['rows'])
    order=[{1}]
    for r in range(1,maxn+1):
        order.append({math.lcm(j,t) for j in range(1,r+1) for t in order[r-j]})
    def H(r,t):
        return max(math.lcm(o,t) for o in order[r])
    reconstructed=[]
    for n in range(7,maxn+1):
        candidates=[dict(kind='two_permutations',gap=2*3**(n-1)),
                    dict(kind='two_singular',gap=4*3**(n-2)-1)]
        for m in range(2,n+1):
            # Enumerate component lengths, not component counts.
            for length in range(2,m+1):
                if m % length:
                    continue
                d=m//length;r=n-m
                c=(2**length+(-1)**length*2)**d*3**r
                period=H(r,m)
                candidates.append(dict(kind='same_cycle',m=m,d=d,r=r,
                                  proper=c,period=period,gap=c-period))
        for occupied in range(2,n+1):
            r=n-occupied
            for a in range(1,occupied//2+1):
                b=occupied-a;d=math.gcd(a,b)
                c=bipartite(a//d,b//d)**d*3**r
                period=max(H(r,a),H(r,b)) if d==1 else H(r,math.lcm(a,b))
                candidates.append(dict(kind='cross_cycles',a=a,b=b,d=d,r=r,
                                  proper=c,period=period,gap=c-period))
        recorded=next(x['cases'] for x in cert['all_cases'] if x['n']==n)
        key=lambda c:json.dumps(c,sort_keys=True)
        check(sorted(map(key,candidates))==sorted(map(key,recorded)),f'Case mismatch n={n}')
        # Direct optimization over all admissible coprime splits; no nearest formula.
        target,a,b=min((bipartite(a,n-a)-(n-a),a,n-a)
                       for a in range(2,n//2+1) if math.gcd(a,n-a)==1)
        check(min(c['gap'] for c in candidates)==target,f'Gap mismatch n={n}')
        recorded_row=next(x for x in cert['rows'] if x['n']==n)
        check((target,a,b)==(recorded_row['deficit'],recorded_row['a'],recorded_row['b']),
              f'Row mismatch n={n}')
        reconstructed.append((n,len(candidates)))
    # Small direct colorings independently audit the palette formula.
    color_tests=0
    for k in range(3,6):
        for a,b in ((1,1),(1,3),(2,2),(2,3)):
            literal=sum(not(set(c[:a]) & set(c[a:]))
                        for c in itertools.product(range(k),repeat=a+b))
            check(literal==bipartite(a,b,k),'Coloring formula failed')
            color_tests+=1
    # Rational arithmetic at the analytic cutoff; monotonicity is proved in text.
    A=2**16; eps=Fraction(32**2,2*A)
    check(eps==Fraction(1,128),'Cutoff ratio')
    margin=(1-eps)*(Fraction(27,2)*A-18)-(Fraction(51,4)*A-6)
    check(margin>0,'Even-class tail comparison')
    summary=dict(status='PASS',rows=len(reconstructed),
        candidates=sum(c for n,c in reconstructed),
        direct_coloring_tests=color_tests,cutoff=32,
        even_tail_margin_at_cutoff=str(margin),
        implementation='Independent DP order sets and inclusion-exclusion coloring count')
    (ROOT/'results/independent_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':
    main()
