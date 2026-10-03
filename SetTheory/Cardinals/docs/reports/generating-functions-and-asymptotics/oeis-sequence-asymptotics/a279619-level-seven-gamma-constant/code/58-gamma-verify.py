#!/usr/bin/env python3
"""Exact and numerical checks for the A279619 report (no network access).
Run: python code/verify.py. Dependencies: sympy, mpmath.
Symbolic/rational assertions are certificates; floating-point tests are diagnostics.
"""
from __future__ import annotations
import csv, json, math
from fractions import Fraction as Q
from pathlib import Path
import sympy as s
import mpmath as mp
R=s.Rational
OUT=Path(__file__).resolve().parents[1]/'data'

def expansion(root: int, order: int) -> list:
    if root not in (27,-1) or order<0:
        raise ValueError('root must be 27 or -1; order must be nonnegative')
    r=R(root); c=[s.Integer(1)]
    def residual(j, current):
        total=s.Integer(0)
        for k, ck in enumerate(current):
            d=j-k
            if d<0: continue
            total+=r*ck*s.binomial(R(1,2)-k,d)
            if d<=2: total-=ck*[26,13,2][d]
            for h,q in enumerate([27,-27,6]):
                if d>=h:
                    total-=ck/r*q*(-1)**(d-h)*s.binomial(-R(3,2)-k,d-h)
        return s.factor(total)
    for m in range(1,order+1):
        c.append(s.factor(residual(m+1,c)/(m*(r+27/r))))
    assert all(residual(j,c)==0 for j in range(order+2))
    return c

def certificates() -> dict:
    def pull(v,J,h,p,q):
        jp=s.diff(J,v)
        return [s.factor(s.diff(jp,v)+(2*h+p)*jp+jp**2*(R(3,2)*J-1)/(J*(1-J))),
                s.factor(s.diff(h,v)+h*h+p*h+q+R(5,144)*jp**2/(J*(1-J)))]
    w=s.symbols('w'); z=(1-w*w)/(27+w*w); dz=s.diff(z,w)
    D=(1-27*z)*(1+z)
    p=s.factor((1-39*z-54*z*z)/(z*D)*dz-s.diff(dz,w)/dz)
    q=s.factor(-(2+6*z)/(z*D)*dz**2)
    T=15*w*w+96*w+85
    h=R(1,4)*(2*w/(w*w+27)-s.diff(T,w)/T)
    J=1728*(1-w)**7*(1+w)/((w*w+27)*T**3)
    vals=pull(w,J,h,p,q)
    m=s.symbols('m'); H=1-m+m*m
    vals+=pull(m,R(27,4)*m*m*(1-m)**2/H**3,-s.diff(H,m)/(4*H),
               (1-2*m)/(m*(1-m)),-1/(4*m*(1-m)))
    x=s.symbols('x'); ph=(1-R(3,2)*x)/(x*(1-x)); qh=-R(5,144)/(x*(1-x))
    vals += [s.factor(s.diff(ph,x)+2*ph**2+4*qh-(1-R(113,36)*x)/(x*x*(1-x))),
             s.factor(2*s.diff(qh,x)+4*ph*qh+R(5,72)/(x*x*(1-x)))]
    D=(1-27*x)*(1+x); pa=(1-39*x-54*x*x)/(x*D); qa=-(2+6*x)/(x*D)
    vals += [s.factor(s.diff(pa,x)+2*pa**2+4*qa-(-1+86*x+186*x*x)/(-x*x*D)),
             s.factor(2*s.diff(qa,x)+4*pa*qa-(4+24*x)/(-x*x*D))]
    assert all(v==0 for v in vals)
    names=['A279619_Fprime','A279619_F','elliptic_Fprime','elliptic_F',
           'Clausen_Hprime','Clausen_H','A183204_Hprime','A183204_H']
    return dict(zip(names,map(str,vals)))

def sequence(nmax: int) -> list[int]:
    a=[1,2]
    for n in range(1,nmax):
        an,rem=divmod((26*n*n+13*n+2)*a[-1]+3*(3*n-1)*(3*n-2)*a[-2],(n+1)**2)
        assert rem==0
        a.append(an)
    return a

def companion(nmax: int) -> list[Q]:
    b=[Q(0),Q(1)]
    for n in range(1,nmax):
        b.append(((26*n*n+13*n+2)*b[-1]+3*(3*n-1)*(3*n-2)*b[-2])/(n+1)**2)
    return b

def atan_bounds(q: int, digits: int) -> tuple[Q,Q]:
    if q<=1: raise ValueError('q must exceed 1')
    total=Q(0); k=0
    while True:
        total+=Q((-1)**k,(2*k+1)*q**(2*k+1))
        nxt=Q((-1)**(k+1),(2*k+3)*q**(2*k+3))
        if abs(nxt)<Q(1,10**digits): return min(total,total+nxt),max(total,total+nxt)
        k+=1

def root_bounds(x: Q,k: int,digits: int) -> tuple[Q,Q]:
    if x<=0 or k<1: raise ValueError('positive radicand and degree required')
    scale=10**digits
    v=int(s.integer_nthroot(x.numerator*scale**k//x.denominator,k)[0])
    lo,hi=Q(v,scale),Q(v+1,scale)
    assert lo**k<=x<=hi**k
    return lo,hi

def constant_bounds(digits: int=120) -> tuple[Q,Q,int]:
    work=digits+20
    a,b=atan_bounds(5,work),atan_bounds(239,work)
    pi=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    sqpi=(root_bounds(pi[0],2,work)[0],root_bounds(pi[1],2,work)[1])
    sq3=root_bounds(Q(3),2,work); p0=root_bounds(Q(189,85),4,work)
    q=Q(64,85**3); term=Q(1); total=Q(0); n=0
    while True:
        total+=term
        term*=q*Q((12*n+1)*(12*n+5),144*(n+1)**2)
        n+=1
        if term<Q(1,10**work): break
    f=(total,total+term/(1-q))
    lo=3*sq3[0]/(8*pi[1]*sqpi[1]*p0[1]*f[1])
    hi=3*sq3[1]/(8*pi[0]*sqpi[0]*p0[0]*f[0])
    assert 0<hi-lo<Q(1,10**digits)
    return lo,hi,n

def decimal_cell(lo: Q,hi: Q,digits: int) -> dict:
    scale=10**digits
    a=lo.numerator*scale//lo.denominator
    b=(hi.numerator*scale+hi.denominator-1)//hi.denominator
    def fixed(v):
        whole,frac=divmod(v,scale)
        return f'{whole}.{frac:0{digits}d}'
    return dict(lower=fixed(a),upper=fixed(b),width_units=str(b-a))

def mpq(x):
    x=Q(str(x)); return mp.mpf(x.numerator)/x.denominator

def write_csv(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

def main():
    OUT.mkdir(exist_ok=True); mp.mp.dps=190
    c,d=expansion(27,12),expansion(-1,12); cert=certificates()
    t=s.symbols('t')
    logpoly=s.series(s.log(sum(c[j]*t**j for j in range(5))),t,0,5).removeO().expand()
    ell=[logpoly.coeff(t,j) for j in range(1,5)]
    a,b=sequence(1000),companion(151)
    assert a[:10]==[1,2,22,336,6006,117348,2428272,52303680,1160427510,26337699740]
    for n in range(100):
        assert a[n]*b[n+1]-a[n+1]*b[n]==Q((-1)**n*math.factorial(3*n),math.factorial(n)*math.factorial(n+1)**2)
    for n in range(41):
        assert sum(a[k]*a[n-k] for k in range(n+1))==sum(math.comb(n,k)**2*math.comb(n+k,n)*math.comb(2*n-k,n) for k in range(n+1))
    lo,hi,nt=constant_bounds(); Llo,Lhi=b[90]/a[90],b[91]/a[91]
    assert 0<Lhi-Llo<Q(1,10**125)
    G=mp.gamma(mp.mpf(1)/7)*mp.gamma(mp.mpf(2)/7)*mp.gamma(mp.mpf(4)/7)
    C=mp.sqrt(3*mp.pi)/G; H=3*G/(8*mp.pi**2)
    assert mpq(lo)<C<mpq(hi)
    q0=mp.mpf(64)/85**3; P0=(mp.mpf(189)/85)**mp.mpf('.25')
    F=mp.hyp2f1(mp.mpf(1)/12,mp.mpf(5)/12,1,q0)
    Fp=mp.mpf(5)/144*mp.hyp2f1(mp.mpf(13)/12,mp.mpf(17)/12,2,q0)
    Chyp=mp.sqrt(mp.mpf(27)/28)*P0*(24*F+798*q0*Fp)/(170*mp.sqrt(mp.pi))
    assert abs(Chyp/C-1)<mp.mpf('1e-170') and abs(P0*F/H-1)<mp.mpf('1e-170')
    L=mpq((b[150]/a[150]+b[151]/a[151])/2); Dmin=G/(56*mp.pi**mp.mpf('1.5'))
    rows=[]
    for n in (20,50,100,250,500,1000):
        for k in (0,1,3,6,12):
            ap=C*mp.mpf(27)**n/mp.mpf(n)**mp.mpf('1.5')*sum(mpq(c[j])/mp.mpf(n)**j for j in range(k+1))
            rows.append(dict(n=n,highest_power=k,relative_error=mp.nstr(ap/a[n]-1,18)))
    write_csv('dominant_errors.csv',rows)
    rows=[]
    for n in (10,20,30,50,75):
        norm=(mpq(b[n])-L*a[n])/((-1)**(n+1)*Dmin/mp.mpf(n)**mp.mpf('1.5'))
        for k in (0,1,3,6,12):
            ap=sum(mpq(d[j])/mp.mpf(n)**j for j in range(k+1))
            rows.append(dict(n=n,highest_power=k,normalized_error=mp.nstr(ap-norm,18)))
    write_csv('minimal_errors.csv',rows)
    lam,beta=mp.log(27),mp.mpf('1.5'); le=list(map(mpq,ell))
    q1=-le[0]/lam; q2=(beta*q1-le[1])/lam; q3=(beta*q2+le[0]*q1-le[2])/lam
    rows=[]
    for n in (20,50,100,500,1000):
        Y=mp.mpf(a[n]); x0=-beta/lam*mp.lambertw(-lam/beta*(C/Y)**(1/beta),-1).real
        for k in range(4):
            x=x0+sum(v/x0**(j+1) for j,v in enumerate([q1,q2,q3][:k]))
            rows.append(dict(n=n,correction_terms=k,x_minus_n=mp.nstr(x-n,18)))
    write_csv('inverse_errors.csv',rows)
    result=dict(exact_certificates=cert,dominant_coefficients=list(map(str,c)),minimal_coefficients=list(map(str,d)),
                log_coefficients=list(map(str,ell)),certified_C_decimal_interval_100_places=decimal_cell(lo,hi,100),
                certified_L_decimal_interval_100_places=decimal_cell(Llo,Lhi,100),
                C_rational_bounds=[str(lo),str(hi)],L_rational_bounds=[str(Llo),str(Lhi)],
                positive_hypergeometric_terms_used=nt,C_gamma_numerical=mp.nstr(C,110),
                boundary_H_numerical=mp.nstr(H,100),L_numerical=mp.nstr(L,110),
                minimal_amplitude_numerical=mp.nstr(Dmin,60),
                checks=dict(sequence_through=1000,wronskians_checked=100,convolution_terms_checked=41,
                            formal_order=12,symbolic_certificates=8,decimal_working_precision=190),
                status='All exact assertions passed. Floating-point comparisons are diagnostics, not proofs.')
    (OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: eight rational ODE identities and order-12 expansions for both roots.')
    print('PASS: 100 Wronskians, 41 convolution identities, exact recurrence through n=1000.')
    print('Certified C interval:',decimal_cell(lo,hi,100))
    print('Certified L interval:',decimal_cell(Llo,Lhi,100))
    print('Files written to',OUT)
if __name__=='__main__': main()
