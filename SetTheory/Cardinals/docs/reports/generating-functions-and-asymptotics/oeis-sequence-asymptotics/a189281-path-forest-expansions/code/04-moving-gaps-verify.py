#!/usr/bin/env python3
"""Independent exact checks, reproducible coefficient tables, rational enclosures."""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import permutations
from math import factorial, comb
from pathlib import Path
import csv, json, random, time
from local_expansions import *

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'data'
checks=Counter()

def check(ok, name):
    if not ok:
        raise AssertionError(name)
    checks[name]+=1

def integer_partitions(n, lo=1):
    if n==0:
        yield ()
    for first in range(lo,n+1):
        for tail in integer_partitions(n-first,first):
            yield (first,)+tail

def test_tilings():
    for n in range(1,10):
        K=min(5,n-1)
        for lengths in integer_partitions(n):
            a=densities(lengths,K)
            exact=exact_tilings(lengths,K)
            formal=normalized_tilings(a,K,K)
            for p in profiles(K):
                c=stats(p)[1]
                value=eval_poly(formal.get(p,[0]),Q(1,n))*n**c
                check(value==exact.get(p,0),'tiling reconstruction')

def test_permutations():
    for n in range(2,8):
        hist={(r,s,t):Counter() for r in range(1,n) for s in range(1,n) for t in (1,2)}
        for p in permutations(range(n)):
            D=defaultdict(int); A=defaultdict(int)
            for r in range(1,n):
                for i in range(n-r):
                    diff=p[i+r]-p[i]
                    A[r,abs(diff)]+=1
                    if diff>0: D[r,diff]+=1
            for r in range(1,n):
                for s in range(1,n):
                    hist[r,s,1][D[r,s]]+=1
                    hist[r,s,2][A[r,s]]+=1
        tilings={r:exact_tilings(offset_lengths(n,r),n-1) for r in range(1,n)}
        for (r,s,t),h in hist.items():
            mu=[Q(0)]*n
            TA,TB=tilings[r],tilings[s]
            for p in TA.keys() & TB.keys():
                k,c,v=stats(p)
                if v<=n:
                    mu[k]+=Q(t**c*pfact(p)*TA[p]*TB[p]*factorial(n-v),factorial(n))
            for k in range(n):
                brute=Q(sum(comb(j,k)*count for j,count in h.items() if j>=k),factorial(n))
                check(mu[k]==brute,'brute-force factorial moment')
            avoid=sum((-1)**k*mu[k] for k in range(n))*factorial(n)
            check(avoid==h[0],'brute-force avoidance')
    # Published initial values used only as a small independent cross-check.
    oeis={1:[1,1,2,5,18,75,410,2729],2:[1,1,2,4,16,44,200,1288]}
    for t in (1,2):
        for n in range(2,8):
            mu=exact_moments(offset_lengths(n,2),offset_lengths(n,2),t,n-1)
            value=sum((-1)**k*mu[k] for k in range(n))*factorial(n)
            check(value==oeis[t][n],'OEIS initial-value check')

def test_corrections():
    rng=random.Random(20261004)
    for trial in range(8):
        a=[Q(rng.randrange(1,10),11) for _ in range(8)]
        b=[Q(rng.randrange(1,10),13) for _ in range(8)]
        for t in (1,2):
            B=corrections(a,b,t,2,extra_check=2)
            lam=t*a[0]*b[0]
            C=2*lam**2-Q(t*t,2)*(a[0]**2*(b[0]+2*b[1])+b[0]**2*(a[0]+2*a[1]))+t*a[1]*b[1]
            check(B[1]==[0,lam,C],'first correction identity')
            check(B[2][4]==C*C/2,'second correction quartic')
            swapped=corrections(b,a,t,2)
            check(B==swapped,'forest swap symmetry')
            chopped=corrections(a[:3],b[:3],t,2)
            check(B==chopped,'locality through order two')
    for q in range(2,6):
        M=q-1
        a=[Q(1,i+2) for i in range(2*M+1)]
        b=[Q(2,i+4) for i in range(2*M+1)]
        for t in (1,2):
            B=corrections(a,b,t,M)
            ap=list(a); ap[q-1]+=Q(1,7)
            changed=corrections(ap,b,t,M)
            h=boundary_polynomial(b,t,q)/7
            for j in range(M+1):
                for l in range(2*j+1):
                    check(changed[j][l]-B[j][l]==(h if j==M and l==q else 0),
                          'highest-path sensitivity')
    for q in range(2,13):
        beta=Q(1,q+2)
        b=[max(1-j*beta,0) for j in range(1,q+1)]
        check(boundary_polynomial(b,1,q)==-beta**2*(1+beta)**(q-2),'nonzero boundary family')

def exp_interval(x, T=100):
    x=Q(x)
    if x<0 or x>=T+2:
        raise ValueError('exp enclosure requires 0 <= x < T+2')
    term=Q(1); lower=Q(1)
    for j in range(1,T+1):
        term*=x/j;lower+=term
    next_term=term*x/(T+1)
    return lower,lower+next_term/(1-x/(T+2))

def outward(q: Q, digits=12, up=False):
    scale=10**digits
    num=q.numerator*scale
    v= -((-num)//q.denominator) if up else num//q.denominator
    sign='-' if v<0 else ''
    v=abs(v)
    return f'{sign}{v//scale}.{v%scale:0{digits}d}'

def generate_tables():
    rays=[(Q(1,2),Q(1,2)),(Q(1,3),Q(1,2)),(Q(2,5),Q(1,2))]
    coeffs=[];certs=[];table=[]
    for alpha,beta in rays:
        a=[max(1-j*alpha,0) for j in range(1,13)]
        b=[max(1-j*beta,0) for j in range(1,13)]
        for t in (1,2):
            B=corrections(a,b,t,6)
            c=[eval_poly(p,-1) for p in B]
            coeffs.append({'alpha':str(alpha),'beta':str(beta),'theta':t,
                           'B':[[str(v) for v in p] for p in B],
                           'avoidance':[str(v) for v in c]})
            for j,v in enumerate(c):
                table.append([str(alpha),str(beta),t,j,str(v)])
            lam=t*a[0]*b[0]
            el,eu=exp_interval(lam)
            for n in [60,120,240,480]:
                r,s=int(n*alpha),int(n*beta)
                mu=matching_target_moments(n,r,s,t,31)
                upper=sum((-1)**k*mu[k] for k in range(31))
                lower=upper-mu[31]
                check(0<=lower<=upper<=1,'Bonferroni ordering')
                approx=sum(c[j]*Q(1,n)**j for j in range(7))
                rl=(el*lower-approx)*n**7
                ru=(eu*upper-approx)*n**7
                check(rl<=ru,'scaled residual ordering')
                certs.append({'alpha':str(alpha),'beta':str(beta),'theta':t,'n':n,
                    'probability_lower':str(lower),'probability_upper':str(upper),
                    'scaled_residual_lower':str(rl),'scaled_residual_upper':str(ru),
                    'decimal_lower':outward(rl),'decimal_upper':outward(ru,up=True)})
    DATA.mkdir(exist_ok=True)
    (DATA/'coefficients.json').write_text(json.dumps(coeffs,indent=2)+'\n')
    (DATA/'certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    with (DATA/'avoidance_coefficients.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['alpha','beta','theta','order','coefficient']);w.writerows(table)
    with (DATA/'certified_residuals.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['alpha','beta','theta','n','lower','upper'])
        for row in certs:
            w.writerow([row['alpha'],row['beta'],row['theta'],row['n'],row['decimal_lower'],row['decimal_upper']])
    print('Selected coefficients:')
    for row in coeffs:
        print(row['alpha'],row['beta'],row['theta'],row['avoidance'])
    print('Selected residual enclosures, n^7 (e^lambda P0 - sum_{j=0}^6 c_j/n^j):')
    for row in certs:
        if row['alpha']=='1/3' and row['theta']==1:
            print(row['n'],row['decimal_lower'],row['decimal_upper'])


def short_path_certificates():
    rows=[]
    el,eu=exp_interval(Q(2))
    for L in (1,2,3):
        for n in (60,120,240,480):
            short=(L,n-L)
            long=(n//2,n-n//2)
            intervals=[]
            for shape in (short,long):
                mu=single_path_target_moments(shape,2,41)
                hi=sum((-1)**k*mu[k] for k in range(41))
                lo=hi-mu[41]
                intervals.append((lo,hi))
            dl=intervals[0][0]-intervals[1][1]
            du=intervals[0][1]-intervals[1][0]
            check(dl<=du<0,'short-path sign certificate')
            lo,hi=eu*dl*n**(L+1),el*du*n**(L+1)
            rows.append([L,n,outward(lo),outward(hi,up=True)])
        for n in (10,20):
            mu=single_path_target_moments((L,n-L),1,n-1)
            for k in range(n):
                expected=Q(comb(n-2,k)*factorial(n-k),factorial(n)) if k<=n-2 else Q(0)
                check(mu[k]==expected,'directed exact shape blindness')
    with (DATA/'short_path_certificates.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['L','n','scaled_lower','scaled_upper']);w.writerows(rows)
    print('Short-path residuals n^(L+1)*e^2*(P_short-P_long), limit -2:')
    for row in rows:
        if row[1] in (60,480): print(*row)

def main():
    start=time.time()
    test_tilings();test_permutations();test_corrections();generate_tables();short_path_certificates()
    report=['All exact checks passed.']+[f'{k}: {v}' for k,v in checks.items()]
    report += [f'Total assertions: {sum(checks.values())}',f'Elapsed seconds: {time.time()-start:.3f}',
               'These computations check finite cases; the all-orders theorem is proved in the article.',
               'No Lean or Rocq formalization was executed.']
    (DATA/'verification.txt').write_text('\n'.join(report)+'\n')
    print('\n'.join(report))

if __name__=='__main__':main()
