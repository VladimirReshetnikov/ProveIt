#!/usr/bin/env python3
"""Exact enumeration and independent numerical tests; no network access.

Run: python verification/verify.py --max-n 20000
Writes tables in data/. Finite tests support, but do not replace, the proofs.
"""
from __future__ import annotations
import argparse,bisect,csv,json,math
from pathlib import Path
import mpmath as mp
from expansion import saddle_polynomials,poly,approximation,inverse_prediction

PREFIX=[1,1,1,1,3,3,4,4,5,12,14,16,19,21,24,27,64,72,84,94,108,120,136,150,169,377,427,480,540,603,674,748,831,918,1014,1115,2432,2702,3009,3331,3692,4070,4494,4935,5427,5942,6510,7104,7760,16475,18138,19928,21873,23961]
SQUARE=[1,1,3,12,64,377,2432,16475,116263,845105,6292069,47759392,368379006,2879998966,22777018771,181938716422,1465972415692,11902724768574,97299665768397,800212617435074,6617003142869419,54985826573015541,458962108485797208,3846526994743330075]
PLUS=[1,1,4,19,108,674,4494,31275,225132,1662894,12541802,96225037,748935563,5900502806,46976736513,377425326138,3056671009814,24930725879856,204623068332997,1688980598900228,14012122025369431,116784468316023069,977437078888272796,8212186058546599006]
MINUS=[1,1,2,7,34,192,1206,8033,55974,403016,2977866,22464381,172388026,1341929845,10573800028,84192383755,676491536028,5479185281572,44692412971566,366844007355202,3028143252035976,25123376972033392,209401287806758273,1752674793617241002]


def enumerate_all(limit:int):
    dp=[0]*(limit+1);dp[0]=1
    a=[0]*(limit+1);a[0]=1
    slices={0:[1],1:[1],-1:[1]};samples={}
    max_m=math.isqrt(limit)
    for m in range(1,max_m+1):
        for n in range(m,limit+1):dp[n]+=dp[n-m]
        for n in range(m*m,min((m+1)**2,limit+1)):a[n]=dp[n]
        for t in (-1,0,1):
            n=m*m+t*m
            if n<=limit:slices[t].append(dp[n])
        if m in (10,20,40,60,80,100,120,140):
            for t in (-1,0,1,2):
                n=m*m+t*m
                if n<=limit:samples[m,t]=dp[n]
    return a,slices,samples


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-n',type=int,default=20000)
    args=parser.parse_args()
    if args.max_n<600:parser.error('--max-n must be at least 600')
    out=Path(__file__).resolve().parents[1]/'data';out.mkdir(exist_ok=True)
    c,P=saddle_polynomials(order=4,dps=80)
    assert abs(P[1][0]-c['d0'])<mp.mpf('1e-65')
    assert abs(P[1][1]-c['eta'])<mp.mpf('1e-65')
    for j in range(5):
        leading=(-1)**j/(mp.factorial(j)*(2*c['B'])**j)
        assert abs(P[j][-1]-leading)<mp.mpf('1e-60')
    a,slices,samples=enumerate_all(args.max_n)
    assert a[:len(PREFIX)]==PREFIX
    for t,ref in [(0,SQUARE),(1,PLUS),(-1,MINUS)]:assert slices[t][:len(ref)]==ref
    assert all(a[n]>=a[n-1] for n in range(1,len(a)))
    print(f'PASS: exact DP through n={args.max_n}; four OEIS prefixes; monotonicity.')
    rows=[]
    for (m,t),exact in samples.items():
        n=m*m+t*m
        errors=[]
        for order in range(5):
            approx=approximation(n,m,c,P,order)
            errors.append(mp.nstr(approx/exact-1,14))
        rows.append([m,t,n,exact]+errors)
    with (out/'shell_errors.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['m','t','n','exact','relative_error_order0','relative_error_order1','relative_error_order2','relative_error_order3','relative_error_order4']);w.writerows(rows)
    print('Shell relative errors: columns m,t, orders 0/1/2/3/4')
    for r in rows:
        if r[0] in (20,40,80,140) and r[1] in (0,2):print(r[:2]+r[4:])
    phase=[]
    for k in (10,20,40,80,100,140):
        for n in (k*k-1,k*k):
            if n>args.max_n:continue
            x=mp.sqrt(n);delta=x-math.isqrt(n)
            R=mp.mpf(n)*a[n]*mp.exp(-c['g']*x)
            L=c['C']*c['s']**delta
            Q1=c['d0']+c['linear']*delta+c['quadratic']*delta**2
            phase.append([n,a[n],mp.nstr(delta,16),mp.nstr(R,18),mp.nstr(L,18),mp.nstr(x*(R/L-1),18),mp.nstr(Q1,18)])
    with (out/'phase_checks.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['n','exact','delta','normalized_R','leading_phase','sqrt_n_times_relative_difference','Q1']);w.writerows(phase)
    boundary=[]
    for k in (10,20,40,80,100,140):
        for r in range(1,7):
            n=k*k-r
            if n>args.max_n:continue
            R=mp.mpf(n)*a[n]*mp.exp(-c['g']*mp.sqrt(n))
            signed=R/c['lower']-1
            first=c['tail']+c['beta']*(r-1)/2
            boundary.append([k,r,n,a[n],mp.nstr(signed,18),mp.nstr(k*signed,18),mp.nstr(first,18)])
    with (out/'boundary_defects.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['k','distance_r','n','exact','relative_defect','k_times_defect','first_coefficient']);w.writerows(boundary)
    print('Boundary comparison at k=140: r, k*(R/(Cs)-1), predicted coefficient')
    for row in boundary:
        if row[0]==140:print(row[1],row[5],row[6])
    inv=[]
    for xint in (20,40,80,120):
        for phase0 in ('.1','.5','.7','.8','.95'):
            x=mp.mpf(xint)+mp.mpf(phase0)
            yf=c['C']*mp.exp(c['g']*x)/x**2
            y=int(mp.ceil(yf))
            index=bisect.bisect_left(a,y)
            if index>=len(a):continue
            predicted=inverse_prediction(y,c)
            inv.append([xint,phase0,y,index,mp.nstr(predicted,18),mp.nstr(index-predicted,14)])
    with (out/'inverse_checks.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['anchor_integer','anchor_phase','integer_threshold_y','exact_inverse','phase_prediction','signed_error']);w.writerows(inv)
    print('Inverse signed errors:')
    for row in inv:print(row[0],row[1],row[-1])
    numeric={k:mp.nstr(v,60) for k,v in c.items() if not callable(v)}
    numeric['P']=[[mp.nstr(x,60) for x in coeff] for coeff in P]
    (out/'constants_and_polynomials.json').write_text(json.dumps(numeric,indent=2)+'\n')
    print('PASS: coefficient cross-checks and Gaussian top-degree identities through order 4.')
    print('Numerical error tables written; asymptotic remainder bounds are proved in article.tex.')


if __name__=='__main__':main()
