#!/usr/bin/env python3
"""Independent computations corroborating, not proving, the research notes."""
import argparse, json, math, pathlib, time
if not __debug__:
    raise SystemExit('Run without -O; assertions are required.')
import mpmath as mp
import sympy as sp

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output-dir',type=pathlib.Path,default=pathlib.Path(__file__).parent)
    args=ap.parse_args(); args.output_dir.mkdir(parents=True,exist_ok=True); start=time.time()
    N=2000; a=[0]*(N+1); a[0]=1
    for k in range(1,N+1):
        for n in range(N,k-1,-1): a[n]+=k*a[n-k]
    prefix=[1,1,2,5,7,15,25,43,64,120,186,288,463,695,1105,1728,2525,3741,5775,8244,12447,18302,26424,37827,54729,78330,111184,159538,225624,315415,444708,618666,858165,1199701,1646076,2288961,3150951,4303995,5870539,8032571,10881794,14749051,19992626]
    assert a[:len(prefix)]==prefix
    for n in range(1,N): assert a[n+1]>a[n]
    for n in range(1,N+1):
        M=(math.isqrt(8*n+1)-1)//2
        assert a[n]>=math.factorial(M)
    p=sp.symbols('p'); polys=[None,p]
    for r in range(1,8): polys.append(sp.expand(p*(1-p)*sp.diff(polys[-1],p)))
    assert sp.expand(polys[2]-p*(1-p))==0
    cf={r:[int(c) for c in sp.Poly(polys[r],p).all_coeffs()] for r in range(1,9)}
    mp.mp.dps=55
    def stats(t, maxr=4):
        K=int(mp.ceil(150/t)); f=mp.mpf(0); cumul=[mp.mpf(0)]*(maxr+1)
        for k in range(1,K+1):
            z=k*mp.exp(-t*k); prob=z/(1+z); f+=mp.log1p(z)
            for r in range(1,maxr+1): cumul[r]+=k**r*mp.polyval(cf[r],prob)
        return f,cumul
    cases=[]
    for n in [50,200,1000,2000]:
        m=mp.sqrt(2*n); t0=mp.log(m)/m
        def mean(t): return stats(t,1)[1][1]-n
        t=mp.findroot(mean,(t0,t0*mp.mpf('1.1')),solver='secant',tol=mp.mpf('1e-45'))
        f,k=stats(t,8); V=k[2]
        approx=mp.exp(f+n*t)/mp.sqrt(2*mp.pi*V)
        edge=1+k[4]/(8*V**2)-5*k[3]**2/(24*V**3)
        mr=-mp.lambertw(-t,-1)/t; w=mr/mp.log(mr)
        err0=mp.mpf(a[n])/approx-1; err1=mp.mpf(a[n])/(approx*edge)-1
        assert abs(mean(t))<mp.mpf('1e-35')
        assert edge>0
        cases.append({'n':n,'t':mp.nstr(t,24),'w':mp.nstr(w,20),'relative_error_leading':mp.nstr(err0,20),'relative_error_first_edgeworth':mp.nstr(err1,20),'leading_error_times_w':mp.nstr(err0*w,20),'edgeworth_error_times_w_squared':mp.nstr(err1*w*w,20)})
    # Exact inverse-derivative recurrence, including the first Sommerfeld terms.
    s=sp.symbols('s'); R={1:1/(s-1)}
    for j in range(1,7): R[j+1]=sp.factor((R[j]+s*sp.diff(R[j],s))/(s-1))
    assert sp.simplify(R[2]+1/(s-1)**3)==0
    assert sp.simplify(R[3]-(2*s+1)/(s-1)**5)==0
    # The printed first Edgeworth coefficient follows directly from Gaussian moments.
    k3,k4,V=sp.symbols('k3 k4 V',positive=True)
    e1=sp.factor(3*k4/(sp.factorial(4)*V**2)-15*k3**2/(2*sp.factorial(3)**2*V**3))
    assert sp.simplify(e1-k4/(8*V**2)+5*k3**2/(24*V**3))==0
    receipt={'status':'all corroborative checks passed','proof_status':'ordinary source notes require independent mathematical review','exact_coefficients':N+1,'oeis_prefix_terms':len(prefix),'strict_monotonicity_checks':N-1,'factorial_lower_bound_checks':N,'saddle_cases':cases,'inverse_derivative_ratios':{str(k):str(v) for k,v in R.items()},'seconds':time.time()-start}
    (args.output_dir/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__': main()
