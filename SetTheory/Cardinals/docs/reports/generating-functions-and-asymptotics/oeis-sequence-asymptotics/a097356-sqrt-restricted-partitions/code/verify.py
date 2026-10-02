"""Reproduce the numerical tables and exact-prefix checks.

Usage: python verify.py --max-m 256 --output results
The numerical mpmath dependency is listed in requirements.txt. All partition
counts and threshold comparisons are exact integers; asymptotic approximations
are evaluated with 80 decimal digits. No Internet access is used.
"""
from __future__ import annotations
import argparse
import bisect
import csv
import json
from pathlib import Path
from math import isqrt
import mpmath as mp
from partition_asymptotics import (Saddle, exact_tables, evaluate_poly,
                                  log_coefficients, inverse_coefficients)
from certificate import certify


def save_csv(path,rows):
    if not rows:
        return
    with path.open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]))
        w.writeheader(); w.writerows(rows)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-m',type=int,default=128)
    ap.add_argument('--output',type=Path,default=Path('results'))
    args=ap.parse_args()
    if args.max_m<16:
        ap.error('--max-m must be at least 16')
    args.output.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=80
    s=Saddle.make()
    rho=-mp.expm1(-s.u)
    gamma=2*s.u/s.H
    D={v:s.coefficients(4,v) for v in (-1,0,1)}
    P=s.phase_polynomials(4)
    L=log_coefficients(D[0]); q=inverse_coefficients(s.H,L)
    for v in range(-4,5):
        assert abs(s.coefficients(1,v)[1]-s.d1(v))<mp.mpf('1e-65')
    for j in range(5):
        assert abs(P[j][0]-D[0][j])<mp.mpf('1e-65')
    a,shifted=exact_tables(args.max_m)
    expected=[1,1,1,1,3,3,4,4,5,12,14,16,19,21,24,27,64,72,84,94,
              108,120,136,150,169,377,427,480,540,603,674,748,831,918,
              1014,1115,2432,2702,3009,3331,3692,4070,4494,4935,5427,
              5942,6510,7104,7760,16475,18138,19928,21873,23961]
    assert a[:len(expected)]==expected,'OEIS A097356 prefix mismatch'
    b_prefix=[1,1,3,12,64,377,2432,16475,116263,845105,6292069,47759392,
              368379006,2879998966,22777018771,181938716422,1465972415692]
    assert shifted[0][:len(b_prefix)]==b_prefix,'A206226 prefix mismatch'
    assert all(a[i]<=a[i+1] for i in range(len(a)-1))
    # d1 and inverse algebra checks, independent closed formulas.
    assert abs(q[1]+L[1]/s.H)<mp.mpf('1e-65')
    assert abs(q[2]+2*L[1]/s.H**2+L[2]/s.H)<mp.mpf('1e-65')
    f=lambda x:mp.nstr(x,30)
    def pack(x):
        if isinstance(x,dict):return {str(k):pack(v) for k,v in x.items()}
        if isinstance(x,list):return [pack(v) for v in x]
        return mp.nstr(x,65)
    constants={'u':s.u,'H':s.H,'d':mp.exp(s.H),'C':s.C,'rho':rho,
               'C_lower':s.C*rho,'V':s.V,'gamma':gamma,
               'endpoint_kappa':s.d1(2)+2+s.H/2,
               'D':D,'P':P,'log_coefficients':L,'inverse_coefficients':q}
    (args.output/'coefficients.json').write_text(json.dumps(pack(constants),indent=2))
    (args.output/'sign_certificate.json').write_text(json.dumps(certify(),indent=2))
    ns=[m for m in (16,32,64,128,256,512) if m<=args.max_m]
    rows=[]
    for sig in (-1,0,1):
        for m in ns:
            exact=shifted[sig][m]
            leading=s.C*mp.exp(s.H*m+sig*s.u)/m**2
            row={'sigma':sig,'m':m,'exact':str(exact)}
            for K in range(5):
                approx=leading*sum(D[sig][j]/mp.mpf(m)**j for j in range(K+1))
                row[f'relative_error_K{K}']=f(approx/exact-1)
            rows.append(row)
    save_csv(args.output/'quadratic_checks.csv',rows)
    floor_rows=[]
    endpoints=[]
    samples=[]
    for m in ns:
        for phase in (mp.mpf(0),mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75')):
            n=int(mp.nint((m+phase)**2))
            t=mp.sqrt(n); theta=t-m
            exact=a[n]
            leading=s.C*mp.exp(s.H*t)/n*rho**theta
            row={'m':m,'n':n,'theta':f(theta),'exact':str(exact)}
            for K in range(5):
                approx=leading*sum(evaluate_poly(P[j],theta)/t**j for j in range(K+1))
                row[f'relative_error_K{K}']=f(approx/exact-1)
            floor_rows.append(row)
        n=(m+1)**2-1
        t=mp.sqrt(n)
        R=mp.mpf(n)*a[n]*mp.exp(-s.H*t)
        endpoints.append({'m':m,'n':n,'R_over_Crho':f(R/(s.C*rho)),
                          'm_times_relative_defect':f(m*(R/(s.C*rho)-1))})
    save_csv(args.output/'floor_checks.csv',floor_rows)
    save_csv(args.output/'endpoint_checks.csv',endpoints)
    exceptions=[]
    for m in ns:
        for r in range(1,5):
            n=(m+1)**2-r
            defect=mp.mpf(n)*a[n]*mp.exp(-s.H*mp.sqrt(n))/(s.C*rho)-1
            kappa=sum(P[1])+r*(s.H-2*s.u)/2
            exceptions.append({'m':m,'distance_before_square':r,'n':n,
                               'relative_defect':f(defect),'first_coefficient':f(kappa)})
    save_csv(args.output/'three_exception_checks.csv',exceptions)
    # Inverse targets are integers, so bisect uses only exact comparisons.
    inverses=[]
    for m in ns[:-1] if len(ns)>1 else ns:
        for eta0 in ('.1','.3','.5','.7','.8','.95'):
            X0=m+mp.mpf(eta0)
            Y=int(mp.floor(s.C*mp.exp(s.H*X0)/X0**2))
            if Y>a[-1]:continue
            Q=bisect.bisect_left(a,Y)
            X=s.core_inverse(Y); k=int(mp.floor(X)); eta=X-k
            phase_t=k+min(eta/gamma,1)
            row={'m':m,'eta':f(eta),'target_Y':str(Y),'exact_inverse':Q,
                 'naive_X_squared_error':f(X**2-Q),
                 'phase_aware_squared_error':f(phase_t**2-Q)}
            if eta<gamma:
                sigma=s.H*eta/s.u
                tau=(-2*eta-s.d1(sigma))/s.u
                root=k*k+sigma*k+tau
                row['interior_root_minus_exact']=f(root-Q)
                row['interior_ceiling_minus_exact']=int(mp.ceil(root))-Q
            else:
                row['interior_root_minus_exact']='plateau'
                row['interior_ceiling_minus_exact']='plateau'
                assert Q==(k+1)**2
            inverses.append(row)
    save_csv(args.output/'inverse_checks.csv',inverses)
    total=0; sums=[]
    sample_indices={int(mp.nint((m+mp.mpf(p))**2)) for m in ns for p in ('0','.5','.9')}
    for n,an in enumerate(a):
        total+=an
        if n in sample_indices:
            k=isqrt(n);theta=mp.sqrt(n)-k
            B=(mp.exp(2*s.u*theta)-1
               +(mp.exp(2*s.u)-1)/(mp.exp(s.H)-1))
            approx=s.C*mp.exp(s.H*k)*B/(s.u*k)
            sums.append({'n':n,'m':k,'theta':f(theta),'exact_sum':str(total),
                         'relative_error':f(approx/total-1)})
    save_csv(args.output/'summatory_checks.csv',sums)
    # Plot data: one representative block and the limiting phase law.
    m=min(args.max_m,128)
    for n in range(m*m,(m+1)**2):
        theta=mp.sqrt(n)-m
        norm=mp.mpf(n)*a[n]*mp.exp(-s.H*mp.sqrt(n))/s.C
        samples.append({'theta':float(theta),'normalized':float(norm),
                        'leading':float(rho**theta),
                        'first':float(rho**theta*(1+evaluate_poly(P[1],theta)/mp.sqrt(n)))})
    (args.output/'plot_data.json').write_text(json.dumps({'block':samples,'gamma':float(gamma)}))
    summary={
      'max_m':args.max_m,'largest_A097356_index':len(a)-1,
      'A097356_prefix_terms_checked':len(expected),
      'A206226_prefix_terms_checked':len(b_prefix),
      'monotonic_adjacent_pairs_checked':len(a)-1,
      'coefficient_closed_form_checks':9,
      'quadratic_numeric_rows':len(rows),'floor_numeric_rows':len(floor_rows),
      'inverse_numeric_rows':len(inverses),
      'certificate':'all exact rational assertions passed',
      'notes':'Numerical agreement is a check, not a replacement for the analytic proofs.'}
    (args.output/'verification_summary.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))
    print('square-subsequence coefficients:',[f(v) for v in D[0]])
    print('inverse coefficients:',[f(v) for v in q])
    print('endpoint rows:',endpoints)

if __name__=='__main__':
    main()
