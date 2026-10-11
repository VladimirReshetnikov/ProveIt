#!/usr/bin/env python3
"""High-precision diagnostics, NOT rigorous interval certificates.
Grouped terms are retained; no integer-relation search is used.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
import mpmath as mp

records=[]
def record(name,lhs,rhs):
    err=abs(lhs-rhs)
    if err>mp.mpf('1e-35'): raise AssertionError(f'{name}: {mp.nstr(err,12)}')
    records.append({'name':name,'absolute_residual':mp.nstr(err,12),
                    'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48)})
    print(name,mp.nstr(err,6),flush=True)

def product_jet(bs,s,r):
    co=[mp.mpf(1)]+[mp.mpf(0)]*r
    for b in bs:
        js=[mp.zeta(s,b,derivative=j)/mp.factorial(j) for j in range(r+1)]
        co=[sum(co[j]*js[k-j] for j in range(k+1)) for k in range(r+1)]
    return co[r]*mp.factorial(r)

def laurent_product(bs,up_to):
    H=len(bs); coeff=[mp.mpf(1)]+[mp.mpf(0)]*(up_to+H)
    for b in bs:
        one=[mp.mpf(1)]+[(-1)**j*mp.stieltjes(j,b)/mp.factorial(j) for j in range(up_to+H)]
        coeff=[sum(coeff[j]*one[k-j] for j in range(k+1)) for k in range(up_to+H+1)]
    return {j-H:coeff[j] for j in range(up_to+H+1)}

def elementary(n,r):
    e=[mp.mpf(1)]+[mp.mpf(0)]*r
    for j in range(1,n+1):
        for k in range(min(r,j),0,-1): e[k]+=e[k-1]/j
    return e

def single_jet(bs,a,r,L=90):
    d=laurent_product(bs,max(r-1,0))
    if r==0: return product_jet(bs,0,0)-a*d[-1]
    out=product_jet(bs,0,r)-a*mp.factorial(r)*d[r-1]
    for l in range(2,L+1):
        es=elementary(l-1,r-1)
        out+=(-a)**l/l*sum(mp.factorial(r)/mp.factorial(r-j)*es[j-1]*product_jet(bs,l,r-j) for j in range(1,min(r,l)+1))
    return out

def single_cauchy(bs,a,N=40,L=90):
    rho=mp.mpf('.025'); orders=range(-len(bs),4)
    accum={r:mp.mpc(0) for r in orders}
    for k in range(N):
        s=rho*mp.exp(2j*mp.pi*(k+mp.mpf('.5'))/N)
        c=mp.mpf(1); val=mp.mpc(0)
        for l in range(L+1):
            if l: c*=(-a)*(s+l-1)/l
            val+=c*mp.fprod(mp.zeta(s+l,b) for b in bs)
        for r in orders: accum[r]+=val/s**r
    return {r:v/N*(mp.factorial(r) if r>=0 else 1) for r,v in accum.items()}

def E_power(b,c,a,L=90,primitive=False):
    return mp.fsum((-a)**l*mp.zeta(l,b)*mp.zeta(l,c)/l*(a/(l+1) if primitive else 1) for l in range(2,L+1))

def K(x): return mp.zeta(-1,x,derivative=1)+(x-x*x)/2+x*mp.log(2*mp.pi)/2

def gamma_head_tail(b,c,a,N=18,L=34,primitive=False):
    if primitive:
        head=mp.fsum((n+b)*(K(c+a/(n+b))-K(c))-a*mp.loggamma(c)-a*a*mp.digamma(c)/(2*(n+b)) for n in range(N))
    else:
        head=mp.fsum(mp.loggamma(c+a/(n+b))-mp.loggamma(c)-a*mp.digamma(c)/(n+b) for n in range(N))
    tail=mp.fsum((-a)**l*mp.zeta(l,N+b)*mp.zeta(l,c)/l*(a/(l+1) if primitive else 1) for l in range(2,L+1))
    return head+tail

def polygamma_head_tail(b,c,a,r,N=18,L=34):
    head=mp.fsum(mp.polygamma(r-1,c+a/(n+b))/(n+b)**r for n in range(N))
    tail=(-1)**r*mp.factorial(r-1)*mp.fsum((-a)**j*mp.rf(r,j)/mp.factorial(j)*mp.zeta(r+j,N+b)*mp.zeta(r+j,c) for j in range(L+1))
    return head+tail

def permsign(p): return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def six_cauchy(h=2,z=None,N=40,L=78):
    a=[mp.mpf('.07'),mp.mpf('.13'),mp.mpf('.20')]; rho=mp.mpf('.02')
    w=[2,1,0]; perms=list(itertools.permutations(range(3))); r=3-h
    coeffs=[mp.mpc(0)]*6
    powers=[[x**j for j in range(L+1)] for x in a]
    moments=[[mp.mpf(0)]+[sum(w[p[i]]*powers[i][j] for i in range(3)) for j in range(1,L+1)] for p in perms]
    for k in range(N):
        s=rho*mp.exp(2j*mp.pi*(k+mp.mpf('.5'))/N)
        base=[]
        for l in range(L+1):
            x=3*s+l-2; d=mp.zeta(x)**h
            if z is not None: d*=mp.polylog(x,z)
            base.append(d)
        for pnum,p in enumerate(perms):
            C=[mp.mpf(1)]
            for l in range(1,L+1):
                C.append(s/l*mp.fsum((-1)**j*moments[pnum][j]*C[l-j] for j in range(1,l+1)))
            val=mp.fsum(C[l]*base[l] for l in range(L+1))
            coeffs[pnum]+=val/s**r/N*mp.factorial(r)
    lhs=sum(permsign(p)*coeffs[i] for i,p in enumerate(perms))
    vand=mp.fprod(a[j]-a[i] for i in range(3) for j in range(i+1,3))
    rhs=mp.factorial(r)*vand/3**h
    if z is not None: rhs*=mp.polylog(1,z)
    return lhs,rhs

def untwist(c,a,t,L=80):
    z=mp.exp(-t)
    L0=mp.polylog(0,z); L0p=mp.diff(lambda s:mp.polylog(s,z),0)
    L1=mp.polylog(1,z); L1p=mp.diff(lambda s:mp.polylog(s,z),1)
    first=L0p*mp.zeta(0,c)+L0*mp.zeta(0,c,derivative=1)
    first-=a*(L1p+mp.stieltjes(0,c)*L1)
    first+=mp.fsum((-a)**l/l*mp.polylog(l,z)*mp.zeta(l,c) for l in range(2,L+1))
    ell=mp.euler+mp.log(t)
    correction=(mp.zeta(0,c,derivative=1)+ell*mp.zeta(0,c))/t
    correction+=a*((ell**2+mp.zeta(2))/2+mp.stieltjes(0,c)*ell-mp.stieltjes(1,c))
    return first,correction

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full',action='store_true',help='include slower independent Cauchy alternants')
    args=parser.parse_args(); mp.mp.dps=60; start=time.monotonic()
    b,c,a=mp.mpf('.8'),mp.mpf('1.2'),mp.mpf('.15')
    for prim in [False,True]:
        power=E_power(b,c,a,primitive=prim)
        record('Gamma_reciprocity'+('_primitive' if prim else ''),gamma_head_tail(b,c,a,primitive=prim),gamma_head_tail(c,b,a,primitive=prim))
        record('Gamma_vs_zeta_product'+('_primitive' if prim else ''),gamma_head_tail(b,c,a,primitive=prim),power)
    for r in [2,3,4]:
        lhs=polygamma_head_tail(b,c,a,r)
        record(f'polygamma_reciprocity_r{r}',lhs,polygamma_head_tail(c,b,a,r))
        value=(-1)**r*mp.factorial(r-1)*mp.fsum((-a)**j*mp.rf(r,j)/mp.factorial(j)*mp.zeta(r+j,b)*mp.zeta(r+j,c) for j in range(90))
        record(f'polygamma_vs_lattice_r{r}',lhs,value)
    circle=single_cauchy([b,c],a)
    record('shifted_double_Hurwitz_residue',circle[-1],-a)
    record('no_second_order_pole',circle[-2],0)
    for r in range(4): record(f'single_Laurent_jet_r{r}',circle[r],single_jet([b,c],a,r))
    if args.full:
        for h in [2,3]:
            lhs,rhs=six_cauchy(h=h); record(f'six_term_pole_order_{h}',lhs,rhs)
        lhs,rhs=six_cauchy(h=2,z=mp.mpf('.4')); record('six_term_polylog_twist',lhs,rhs)
    cc=mp.mpf('.9'); aa=mp.mpf('.12'); target=single_jet([mp.mpf(1),cc],aa,1)
    limits=[]
    for tt in ['.1','.01','.001','.0001']:
        val,counter=untwist(cc,aa,mp.mpf(tt))
        limits.append({'t':tt,'finite_part_before_compensation':mp.nstr(val,35),'counterterm':mp.nstr(counter,35),
                       'compensated':mp.nstr(val-counter,35),'error_to_limit':mp.nstr(abs(val-counter-target),14)})
        print('untwist',tt,limits[-1]['error_to_limit'],flush=True)
    if not all(mp.mpf(limits[i+1]['error_to_limit'])<mp.mpf(limits[i]['error_to_limit']) for i in range(3)):
        raise AssertionError('limit diagnostic did not improve')
    out={'evidence':'floating-point diagnostics, not rigorous enclosures or analytic proofs','mpmath_version':mp.__version__,
         'working_decimal_digits':mp.mp.dps,'full_mode':args.full,'equality_tests_passed':len(records),'acceptance_threshold':'1e-35',
         'maximum_observed_absolute_residual':mp.nstr(max(mp.mpf(x['absolute_residual']) for x in records),12),
         'tests':records,'untwisting_limit':{'target':mp.nstr(target,48),'rows':limits},'elapsed_seconds':round(time.monotonic()-start,3)}
    path=Path(__file__).resolve().parents[1]/'results'/'numerical_checks.json'; path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['equality_tests_passed','maximum_observed_absolute_residual','elapsed_seconds']}),flush=True)
if __name__=='__main__': main()
