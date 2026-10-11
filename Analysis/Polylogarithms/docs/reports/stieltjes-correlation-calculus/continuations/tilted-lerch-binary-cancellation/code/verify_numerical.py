#!/usr/bin/env python3
"""Independent floating-point diagnostics, NOT certified error enclosures.

Run: python code/verify_numerical.py --dps 45
All contour truncations, series lengths, thresholds, and versions are logged.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
import time
from pathlib import Path
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
RECORDS=[]
DPS=45

def scalar(x):
    return {'real':mp.nstr(mp.re(x),DPS),'imag':mp.nstr(mp.im(x),DPS)}

def record(name,lhs,rhs,**settings):
    absolute=abs(lhs-rhs); normalized=absolute/max(1,abs(lhs),abs(rhs))
    threshold=mp.mpf(10)**(-(DPS-14))
    item={'name':name,'lhs':scalar(lhs),'rhs':scalar(rhs),
          'absolute_residual':mp.nstr(absolute,10),'normalized_residual':mp.nstr(normalized,10),
          'acceptance_threshold':mp.nstr(threshold,5),'passed':bool(normalized<threshold),**settings}
    RECORDS.append(item)
    print(f"{name}: {mp.nstr(normalized,5)} {'PASS' if item['passed'] else 'FAIL'}",flush=True)
    if not item['passed']:
        raise AssertionError(json.dumps(item,indent=2))

def weights(tilts):
    if len(set(tilts)) != len(tilts):
        raise ValueError('Distinct weights require distinct tilts; use confluent_master.')
    return [mp.fprod(mp.pi/mp.sin(mp.pi*(v-w)) for k,w in enumerate(tilts) if k!=j)
            for j,v in enumerate(tilts)]

def eta(w,a):
    if w==1: return (mp.digamma((a+1)/2)-mp.digamma(a/2))/2
    return mp.power(2,-w)*(mp.zeta(w,a/2)-mp.zeta(w,(a+1)/2))

def master(w,a,tilts,mu=0,jet=0):
    coeff=weights(tilts); r=len(tilts); eps=(-1)**r
    if mu==0:
        if r%2:
            return mp.fsum(A*mp.diff(lambda v:eta(v,a+l),w,jet) for A,l in zip(coeff,tilts))
        if w==1:
            if jet==0: return mp.fsum(A*mp.digamma(a+l) for A,l in zip(coeff,tilts))
            if any(mp.im(a+l) for l in tilts):
                raise ValueError('This diagnostic uses mpmath.stieltjes only at real arguments.')
            return (-1)**(jet+1)*mp.fsum(A*mp.stieltjes(jet,a+l) for A,l in zip(coeff,tilts))
        return -mp.fsum(A*mp.zeta(w,a+l,derivative=jet) for A,l in zip(coeff,tilts))
    def expr(v):
        return -eps*mp.exp(mu)*mp.fsum(A*mp.exp(l*mu)*mp.lerchphi(eps*mp.exp(mu),v,a+l)
                                       for A,l in zip(coeff,tilts))
    return mp.diff(expr,w,jet) if jet else expr(w)

def contour(orders,shifts,tilts,mu=0,spectral_indices=(),moment_indices=(),c=None):
    r=len(orders)
    low=max(mp.re(l)+max(0,1-mp.re(a)) for a,l in zip(shifts,tilts))
    high=1+min(mp.re(l) for l in tilts)
    if low>=high: raise ValueError('No common transform strip')
    if c is None: c=(low+high)/2
    if not low<c<high: raise ValueError('Invalid contour abscissa')
    cutoff=max(mp.mpf(20),(DPS+20)*mp.log(10)/(r*mp.pi))
    def f(t):
        p=c+1j*t
        q=[p+a-1-l for a,l in zip(shifts,tilts)]
        val=mp.exp(p*mu)*mp.fprod(mp.pi/mp.sin(mp.pi*(p-l))*qq**(-s)
                                for s,l,qq in zip(orders,tilts,q))
        for j in spectral_indices: val*=-mp.log(q[j])
        counts={j:moment_indices.count(j) for j in set(moment_indices)}
        for j,n in counts.items():
            z=p-tilts[j]; sj=orders[j]
            h=mp.pi*mp.cot(mp.pi*z)+sj/q[j]
            if n==1: val*=h
            elif n==2: val*=h*h+mp.pi**2/mp.sin(mp.pi*z)**2+sj/q[j]**2
            else: raise ValueError('Only moment multiplicities <=2 are implemented')
        return val
    cuts=[-cutoff,-8,-4,-2,-1,0,1,2,4,8,cutoff]
    value=mp.quad(f,cuts)/(2*mp.pi)
    return value,{'contour_real_part':mp.nstr(c,12),'contour_imaginary_cutoff':mp.nstr(cutoff,12)}

def confluent_master(w,a,distinct,multiplicities):
    """Hermite formula at mu=0; chosen test tilts lie in (-1/2,1/2)."""
    r=sum(multiplicities); eps=(-1)**r; alpha=mp.mpf(r-2)/2
    nodes=[mp.exp(2j*mp.pi*l) for l in distinct]
    def H(z):
        lam=mp.log(z)/(2j*mp.pi)
        core=eta(w,a+lam) if r%2 else mp.zeta(w,a+lam)
        return z**alpha*core
    dd=0
    for j,(z,m) in enumerate(zip(nodes,multiplicities)):
        def quot(t):
            return H(t)/mp.fprod((t-v)**n for k,(v,n) in enumerate(zip(nodes,multiplicities)) if k!=j)
        dd+=mp.diff(quot,z,m-1)/mp.factorial(m-1)
    return -eps*(2j*mp.pi)**(r-1)*mp.exp(1j*mp.pi*sum(m*l for m,l in zip(multiplicities,distinct)))*dd

def anchor_coeffs(orders,deltas,nmax):
    B=[mp.mpf(1)]
    for n in range(1,nmax+1):
        B.append(mp.fsum((-1)**k*mp.fsum(s*d**k for s,d in zip(orders,deltas))*B[n-k]
                         for k in range(1,n+1))/n)
    return B

def convolution(a,b):
    return [mp.fsum(a[k]*b[n-k] for k in range(n+1)) for n in range(len(a))]

def main():
    global DPS
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=45)
    args=parser.parse_args()
    if args.dps<35: parser.error('Use at least 35 working digits')
    DPS=args.dps;mp.mp.dps=DPS
    start=time.time();q=mp.mpf
    # Finite masters: integer, negative, complex orders and complex tilts.
    cases=[([q('.3'),q('1.2')],q('1.2'),[q('.25'),q('0')],q('-.7')),
           ([q('.3'),q('1.2')],q('1.2'),[q('.25'),q('0')],q('.5')),
           ([q('-.4')+q('.2')*1j,q('.8')],q('1.1'),[q('-.12'),q('.23')],0),
           ([q('-.3'),q('.5'),q('.9')],q('1.2'),[q('0'),q('.15'),q('.3')],0),
           ([q('.2'),q('.3'),q('.4'),q('.7')],q('1.3'),[q('-.12'),q('0'),q('.14'),q('.27')],0),
           ([q('.2')+q('.1')*1j,q('.7'),q('-.4')],q('1.4'),[q('-.1')+q('.1')*1j,q('.08'),q('.3')-q('.04')*1j],0)]
    for j,(s,a,l,mu) in enumerate(cases):
        lhs,settings=contour(s,[a+v for v in l],l,mu)
        record(f'matched_master_{j+1}',lhs,master(sum(s),a,l,mu),**settings)
    # Interior Fourier annihilators and the two first nonzero edge coefficients.
    for r in range(2,5):
        l=[q('-.13')+q(j)*q('.41')/(r-1) for j in range(r)]
        coeff=weights(l)
        interior=[mp.fsum(A*mp.exp(1j*mp.pi*ell*v) for A,v in zip(coeff,l))
                  for ell in range(-(r-2),r-1,2)]
        record(f'Fourier_interior_annihilators_depth_{r}',max(abs(v) for v in interior),0)
        for sign in (-1,1):
            lhs=mp.fsum(A*mp.exp(sign*1j*mp.pi*r*v) for A,v in zip(coeff,l))
            rhs=(sign*2j*mp.pi)**(r-1)*mp.exp(sign*1j*mp.pi*sum(l))
            record(f'Fourier_edge_depth_{r}_sign_{sign}',lhs,rhs)
    # All-order Stieltjes jets at a cancelled Hurwitz pole.
    l=[q('-.1'),q('.2')];a=q('1.1')
    for degree in range(4):
        lhs,settings=contour([q('.4'),q('.6')],[a+v for v in l],l,spectral_indices=(0,)*degree)
        record(f'Stieltjes_jet_{degree}',lhs,master(1,a,l,jet=degree),**settings)
    for r,l in [(2,[q('-.1'),q('.2')]),(3,[q('0'),q('.13'),q('.3')])]:
        a=q('1.2');s=[mp.mpf(0)]*r
        lhs,settings=contour(s,[a+v for v in l],l,spectral_indices=(0,))
        coeff=weights(l)
        if r%2==0: rhs=-mp.fsum(A*mp.loggamma(a+v) for A,v in zip(coeff,l))
        else: rhs=mp.fsum(A*(mp.loggamma((a+v)/2)-mp.loggamma((a+v+1)/2)-mp.log(2)/2) for A,v in zip(coeff,l))
        record(f'Gamma_order_jet_depth_{r}',lhs,rhs,**settings)
    # Fully and partially repeated tilts, evaluated without singular weights.
    for distinct,mults in [([q('.12')],[2]),([q('.12')],[3]),([q('.12')],[4]),
                           ([q('0'),q('.21')],[2,1]),([q('-.1'),q('.2')],[2,2]),
                           ([q('-.15'),q('.05'),q('.27')],[1,2,1])]:
        l=[v for v,n in zip(distinct,mults) for _ in range(n)]
        a=q('1.3');s=[q('.7')/len(l)]*len(l)
        lhs,settings=contour(s,[a+v for v in l],l)
        record(f'confluent_{len(RECORDS)}',lhs,confluent_master(sum(s),a,distinct,mults),**settings)
    # Single-anchor expansion: arbitrary independent shifts and order jets.
    l=[q('-.12'),q('.18')];A=q('1.3');deltas=[q('.06'),q('-.08')];s=[q('.4'),q('.9')]
    a=[A+v+d for v,d in zip(l,deltas)];W=sum(s);nmax=max(65,math.ceil(DPS*1.5))
    B=anchor_coeffs(s,deltas,nmax)
    Ms=[[master(W+n,A,l,jet=j) for n in range(nmax+1)] for j in range(3)]
    logs=[[q(0)]+[(-1)**n*d**n/n for n in range(1,nmax+1)] for d in deltas]
    B0=convolution(B,logs[0]);B1=convolution(B,logs[1]);B01=convolution(B0,logs[1])
    rhs0=mp.fsum(b*v for b,v in zip(B,Ms[0]))
    rhs1=mp.fsum(B0[n]*Ms[0][n]+B[n]*Ms[1][n] for n in range(nmax+1))
    rhs2=mp.fsum(B01[n]*Ms[0][n]+(B0[n]+B1[n])*Ms[1][n]+B[n]*Ms[2][n] for n in range(nmax+1))
    for indices,rhs in [((),rhs0),((0,),rhs1),((0,1),rhs2)]:
        lhs,settings=contour(s,a,l,spectral_indices=indices)
        record(f'anchor_independent_jet_{len(indices)}',lhs,rhs,series_last_index=nmax,**settings)
    # A terminated anchor series with negative grouped orders.
    l=[q('-.1'),q('.06'),q('.22')];A=q('1.4');h=q('.17');k=q('-.12');s=[q('.65'),q(-2),q(-1)]
    a=[A+l[0],A+l[1]+h,A+l[2]+k];B=[1,2*h+k,h*h+2*h*k,h*h*k]
    lhs,settings=contour(s,a,l)
    record('finite_negative_order_closure',lhs,mp.fsum(b*master(sum(s)+n,A,l) for n,b in enumerate(B)),**settings)
    # Raw moments require a shift-derivative correction.
    l=[q('-.1'),q('.2')];a=q('1.3');s=[q('.4'),q('.7')];W=sum(s)
    def varmaster(v,w=W):return master(w,a,[v,l[1]])
    correction=s[0]*master(W+1,a,l)
    rhs=mp.diff(varmaster,l[0])+correction
    lhs,settings=contour(s,[a+v for v in l],l,moment_indices=(0,))
    record('raw_first_moment',lhs,rhs,**settings)
    missing_gap=abs(lhs-mp.diff(varmaster,l[0]))
    if missing_gap<q('0.01'):raise AssertionError('Negative control unexpectedly small')
    RECORDS.append({'name':'negative_control_missing_shift_derivative','passed':True,
                    'detected_absolute_error':mp.nstr(missing_gap,12),'expected_nonzero_correction':scalar(correction)})
    rhs2=mp.diff(varmaster,l[0],2)+2*s[0]*mp.diff(lambda v:varmaster(v,W+1),l[0])+s[0]*(s[0]+1)*master(W+2,a,l)
    lhs2,settings=contour(s,[a+v for v in l],l,moment_indices=(0,0))
    record('raw_second_moment',lhs2,rhs2,**settings)
    firsts=[]
    for j in range(2):
        def variation(v):
            ll=l.copy();ll[j]=v;return master(W,a,ll)
        firsts.append(mp.diff(variation,l[j])+s[j]*master(W+1,a,l))
    record('moment_conservation_at_zero',sum(firsts),0)
    # Explicit rational shifts and genuine real defining integrals.
    for N in range(4):
        l=[q('.5'),q(0)];a=q(N)+q('.5');w=q('.7')+q('.1')*1j
        hn=lambda n:mp.fsum(q(j)**(-w) for j in range(1,n+1))
        rhs=mp.pi*((2**w-2)*mp.zeta(w)-2**w*hn(2*N)+2*hn(N))
        record(f'half_shift_harmonic_{N}',master(w,a,l),rhs)
        gamma=mp.pi*mp.log(mp.sqrt(mp.pi)*mp.binomial(2*N,N)/4**N)
        record(f'half_shift_Gamma_{N}',master(0,a,l,jet=1),gamma)
    l=[q('.5'),q(0)];a=q('.25');w=q('.7')
    beta_integral=mp.quad(lambda u:1/mp.cosh(u**(1/w)),[0,1,3,8,mp.inf])/(2*mp.gamma(w+1))
    record('quarter_shift_beta',master(w,a,l),mp.pi*4**w*beta_integral)
    for numerator,denominator in [(1,2),(2,3),(3,4),(2,5)]:
        y=q('.37');w=q('.7')+q('.13')*1j
        alpha=q(numerator)/denominator;omega=mp.exp(2j*mp.pi/denominator)
        root=mp.power(-y,1/q(denominator))
        lhs=y*mp.lerchphi(-y,w,alpha)
        rhs=mp.power(denominator,w-1)*y*mp.power(-y,-alpha)*mp.fsum(
            omega**(-numerator*j)*mp.polylog(w,omega**j*root) for j in range(denominator))
        record(f'polylog_root_filter_{numerator}_{denominator}',lhs,rhs)
    limit=(DPS+12)*mp.log(10)
    realint=4*mp.quad(lambda u:mp.log1p(mp.exp(2*u))*mp.atan(mp.exp(-u)),[-limit,-8,-2,0,2,8,limit])
    record('defining_log_arctangent_integral',realint,mp.pi**3/3,logarithmic_cutoff=mp.nstr(limit,10))
    delta=q('.3');limit=(DPS+12)*mp.log(10)/(1-delta)
    for moment in (0,1,2):
        val=mp.quad(lambda x:x**moment*mp.exp((1+delta)*x)/(1+mp.exp(x))**2,[-limit,-8,-2,0,2,8,limit])
        rhs=mp.diff(lambda d:mp.pi*d/mp.sin(mp.pi*d),delta,moment)
        record(f'defining_logistic_moment_{moment}',val,rhs,logarithmic_cutoff=mp.nstr(limit,10))
    # Anchored repeated primitives, including resonant W.
    a0=q('1.1');a1=q('1.4');l=[q('-.1'),q('.2')]
    for depth,ell in [(1,1),(2,1),(2,2),(3,2)]:
        def F(a):return master(ell-depth,a,l,jet=1)
        remainder=F(a1)-mp.fsum((a1-a0)**j/mp.factorial(j)*mp.diff(F,a0,j) for j in range(depth))
        rhs=(-1)**ell*remainder/(mp.factorial(ell-1)*mp.factorial(depth-ell))
        lhs=mp.quad(lambda b:(a1-b)**(depth-1)*master(ell,b,l),[a0,a1])/mp.factorial(depth-1)
        record(f'anchored_primitive_depth_{depth}_W_{ell}',lhs,rhs)
    # New six-dimensional logarithmic-remainder integral: independent contour.
    nodes=[0,1,2,4,5,7,8];l=[q(0)]*7;s=[q(1)]*7;shifts=[q(n+1) for n in nodes]
    lhs,settings=contour(s,shifts,l)
    P=mp.pi**2
    rhs=q(11)/516096*P**3+q(1138070753)/5852528640000*P**2+q(31111437326981)/68825736806400000*P+q(24335931370253514869)/56657346539028480000000
    record('mixed_parity_six_dimensional_value',lhs,rhs,**settings)
    residuals=[q(t['normalized_residual']) for t in RECORDS if 'normalized_residual' in t]
    result={'status':'PASS','working_decimal_digits':DPS,'diagnostics':len(RECORDS),
            'positive_comparisons':len(residuals),'negative_controls':len(RECORDS)-len(residuals),
            'largest_normalized_residual':mp.nstr(max(residuals),12),
            'evidence_limit':'Floating-point diagnostics with finite integration/series truncations; NOT interval certificates.',
            'mpmath_version':mp.__version__,'python_version':platform.python_version(),
            'elapsed_seconds':round(time.time()-start,3),'records':RECORDS}
    (ROOT/'data'/f'numerical_results_{DPS}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))

if __name__=='__main__':main()
