#!/usr/bin/env python3
"""Independent checks using direct composition and Lagrange saddle coordinates.

Does not import the author's generators. Outputs are numerical validation, not
interval certificates for quadrature rounding errors.
"""
import hashlib, json, math
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
OUT=Path(__file__).resolve().parent
mp.mp.dps=110

def convolution(a,b,N):
    c=[0]*(N+1)
    for i,ai in enumerate(a[:N+1]):
        for j,bj in enumerate(b[:N+1-i]): c[i+j]+=ai*bj
    return c

def compose_zero_power(q,alpha,N):
    """(1+q)^alpha, q[0]=0, with exact alpha accepted."""
    total=[0]*(N+1); total[0]=1
    power=[0]*(N+1); power[0]=1
    binom=1
    for k in range(1,N+1):
        power=convolution(power,q,N)
        binom=binom*(alpha-k+1)/k
        total=[t+binom*p for t,p in zip(total,power)]
    return total

def compose_log(q,N):
    total=[0]*(N+1)
    power=[0]*(N+1); power[0]=1
    for k in range(1,N+1):
        power=convolution(power,q,N)
        total=[t+sp.Rational((-1)**(k+1),k)*p for t,p in zip(total,power)]
    return total

def phase_direct(x,y,lam,N):
    # X(y(1+s))-x = log(1 + p*(exp(-ys)-1)), p=x/(lam*y).
    # This comes directly from the defining logarithm, without logistic derivatives.
    q=[0]+[x*(-y)**j/(lam*y*sp.factorial(j)) for j in range(1,N+1)]
    L=compose_log(q,N)
    U=[0]+[L[j]/x for j in range(1,N+1)]
    LU=compose_log(U,N)
    return [0]+[sp.Rational((-1)**j,j)-lam*LU[j] for j in range(1,N+1)]

def lagrange_coefficients(f,B,J,exact=False):
    """Change coordinate to v=s sqrt(2f(s)/(B*s^2)), then Gaussian moments."""
    ds=[]
    for j in range(J+1):
        N=2*j
        q=[0]+[2*f[k+2]/B for k in range(1,N+1)]
        alpha=-sp.Rational(2*j+1,2) if exact else -mp.mpf(2*j+1)/2
        power=compose_zero_power(q,alpha,N)
        g=sum((-1)**a*(a+1)*power[N-a] for a in range(N+1))
        mom=sp.factorial2(2*j-1) if exact else mp.factorial(2*j)/(2**j*mp.factorial(j))
        d=(-1)**j*mom*g/B**j
        ds.append(sp.expand(d) if exact else d)
    return [ds[0]]+[ds[j]+ds[j-1] for j in range(1,J+1)]

def saddle(lam=mp.mpf(1),s=mp.mpf(0)):
    f=lambda y:mp.log(1+mp.exp(-s-y))-lam*y/(1+mp.exp(s+y))
    if s:
        yy=saddle(lam)[1]
        y=mp.findroot(f,yy)
    else:
        lo=mp.mpf('1e-20'); hi=max(4/lam,4)
        while f(hi)>0: hi*=2
        for _ in range(430):
            mid=(lo+hi)/2
            if f(mid)>0:lo=mid
            else:hi=mid
        y=(lo+hi)/2
    x=mp.log(1+mp.exp(-s-y)); p=1/(1+mp.exp(s+y))
    return x,y,1+1/lam-y*(1-p)

def row(m):
    # Explicit inclusion-exclusion for surjections, independent of Stirling recurrence.
    return [sum((-1)**(k-j)*math.comb(k,j)*j**m for j in range(k+1)) for k in range(m+1)]

def integer_value(m,n,s=mp.mpf(0)):
    T=row(m)
    if not s:return sum(T[k]*k**n for k in range(m+1))
    return mp.fsum(mp.mpf(T[k])*k**n*mp.exp(s*k) for k in range(m+1))

def outnum(v): return mp.nstr(v,75)

result={}
xs,ys=sp.symbols('x y')
phase=phase_direct(xs,ys,sp.Integer(1),10)
stored={}
for line in (ROOT/'phase_coefficients.txt').read_text().splitlines():
    name,value=line.split(' = '); stored[int(name[2:])]=sp.sympify(value)
for j in range(11):assert sp.expand(phase[j]-stored[j])==0,(j,phase[j],stored[j])
result['exact_phase_composition']='PASS through f10; no imported generator'

Bsym=sp.Symbol('B'); fs={k:sp.Symbol('f'+str(k)) for k in range(3,11)}
farr=[0,0,Bsym/2]+[fs[k] for k in range(3,11)]
exact=lagrange_coefficients(farr,Bsym,4,True)
export={}
for line in (ROOT/'exact_coefficients.txt').read_text().splitlines():
    if line.startswith('c_') and '(x,y)' not in line:
        name,value=line.split(' = ');export[int(name[2:])]=sp.sympify(value)
for j in range(5):
    assert sp.expand(exact[j]-export[j])==0,j
    assert not sp.sympify(exact[j]).atoms(sp.Float)
result['exact_coefficient_lagrange_inversion']='PASS c0 through c4 symbolically'

x,y,B=saddle()
ff=mp.taylor(lambda t:-mp.log(1+t)-mp.log(mp.log(1+mp.exp(-y*(1+t)))/x),0,16)
co=lagrange_coefficients(ff,B,7)
author=json.loads((ROOT/'numerical_results.json').read_text())
differences=[abs(v-mp.mpf(author['coefficients'][j])) for j,v in enumerate(co)]
assert max(differences)<mp.mpf('1e-73'),max(differences)
result['c0_through_c7_independent_110_digit']=[outnum(v) for v in co]
result['max_coefficient_difference']=outnum(max(differences))

# Direct contour evaluated at c values unrelated to the saddle, including n=1.
contours=[]
for m,n,c,Tmult,s in [(1,1,mp.mpf('.3'),6,0),(2,1,mp.mpf('1.7'),4,0),
        (2,3,mp.mpf('.8'),3,0),(3,2,mp.mpf('1.4'),3,0),
        (10,10,y,1,0),(12,8,mp.mpf('.9'),1,0),
        (5,7,mp.mpf('1.1'),3,mp.mpc('.02','.03'))]:
    s=mp.mpc(s);T=Tmult*mp.pi
    Xc=mp.log(1+mp.exp(-s-c))
    floor=mp.log(1+mp.exp(-mp.re(s)-c))
    scale=abs(Xc)**(-m)*c**(-n)
    fn=lambda t:mp.log(1+mp.exp(-s-c-1j*t))**(-m)*(c+1j*t)**(-n-2)/scale
    cuts=[k*mp.pi/8 for k in range(-8*Tmult,8*Tmult+1)]
    finite=mp.mpf(n+1)/(2*mp.pi*m)*mp.quad(fn,cuts)
    exactv=integer_value(m,n,s)/(mp.factorial(m)*mp.factorial(n)*scale)
    bound=floor**(-m)*(c*c+T*T)**(-mp.mpf(n)/2)/(mp.pi*m*T*scale)
    error=abs(finite-exactv)
    assert error<=bound,(m,n,c,error,bound)
    contours.append(dict(m=m,n=n,c=outnum(c),marking_s=outnum(s),T_over_pi=Tmult,
                         error=outnum(error),analytic_tail_bound=outnum(bound),error_over_bound=outnum(error/bound)))
result['contour_checks']=contours

# Compact-direction expansion; coefficients rebuilt separately at each lambda.
directions=[]
for m,n in [(40,80),(80,40),(60,80),(100,80),(100,100)]:
    lam=mp.mpf(m)/n; xx,yy,bb=saddle(lam)
    ff=mp.taylor(lambda t:-mp.log(1+t)-lam*mp.log(mp.log(1+mp.exp(-yy*(1+t)))/xx),0,10)
    cc=lagrange_coefficients(ff,bb,4)
    lead=mp.factorial(m)*mp.factorial(n)*xx**(-m)*yy**(-n)/(lam*yy*mp.sqrt(2*mp.pi*n*bb))
    ratio=mp.mpf(integer_value(m,n))/lead
    directions.append(dict(m=m,n=n,lambda_=outnum(lam),B=outnum(bb),
                     scaled_order3_residual=outnum((ratio-sum(cc[j]/n**j for j in range(4)))*n**4),
                     c4=outnum(cc[4])))
result['direction_checks']=directions

# Complex marking on a fixed small disk; both phases and exact sums are complex.
markings=[]
for s in [mp.mpc('.02',0),mp.mpc(0,'.02'),mp.mpc('-.02','.02')]:
    xx,yy,bb=saddle(s=s)
    ff=mp.taylor(lambda t:-mp.log(1+t)-mp.log(mp.log(1+mp.exp(-s-yy*(1+t)))/xx),0,10)
    cc=lagrange_coefficients(ff,bb,4)
    for n in [40,80]:
        lead=mp.factorial(n)**2*(xx*yy)**(-n)/(yy*mp.sqrt(2*mp.pi*n*bb))
        ratio=integer_value(n,n,s)/lead
        markings.append(dict(s=outnum(s),n=n,scaled_order3_residual=outnum((ratio-sum(cc[j]/n**j for j in range(4)))*n**4),c4=outnum(cc[4])))
result['complex_marking_checks']=markings

mu=1/y;sig2=(B-1)/(B*y*y);mu0=(B-1)/(B*y)-(B-1-x/y)/(2*B*B)
moments=[]
for n in [40,80,160,320]:
    terms=[v*k**n for k,v in enumerate(row(n))];total=sum(terms)
    mean=mp.fsum(mp.mpf(k)*v for k,v in enumerate(terms))/total
    var=mp.fsum((k-mean)**2*v for k,v in enumerate(terms))/total
    moments.append(dict(n=n,mean_constant=outnum(mean-mu*n),mean_error_scaled=outnum((mean-mu*n-mu0)*n),variance_constant=outnum(var-sig2*n)))
result['moment_checks']=moments

C=1/(y*mp.sqrt(2*mp.pi*B));D=1/(x*y)
inverses=[]
for n in [20,80,320]:
    L=mp.log(integer_value(n,n));w=mp.lambertw(L*mp.sqrt(D)/(2*mp.e));v0=L/(2*w)
    first=v0-(mp.log(v0)/2+mp.log(2*mp.pi*C))/(2*(w+1))
    for J in [0,1,2,4,6]:
        H=lambda v:2*mp.loggamma(v+1)+v*mp.log(D)-mp.log(v)/2+mp.log(C)+mp.log(mp.fsum(co[j]*v**(-j) for j in range(J+1)))
        v=mp.findroot(lambda v:H(v)-L,v0)
        newton=v0;r=math.ceil(math.log2(J+2))
        for _ in range(r):newton-=(H(newton)-L)/mp.diff(H,newton)
        inverses.append(dict(n=n,J=J,iterations=r,initializer_error=outnum(v0-n),first_scaled_error=outnum((first-n)*n*mp.log(n)),inverse_scaled_error=outnum((v-n)*n**(J+1)*mp.log(n)),newton_minus_exact_root=outnum(newton-v)))
result['inverse_checks']=inverses

# Check prime-power periods against full exact inclusion-exclusion values.
# This uses neither the author's modular recurrence nor a truncated k sum.
modular=[]
exact_values={}
for p,r in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(7,2),(11,1),(13,1)]:
    modulus=p**r;period=(p-1)*p**(r-1)
    for n in range(r,r+16):
        for index in (n,n+period):
            if index not in exact_values:exact_values[index]=integer_value(index,index)
        assert (exact_values[n+period]-exact_values[n])%modulus==0,(p,r,n)
    modular.append(dict(p=p,r=r,period=period,first_n=r,last_n=r+15))
result['prime_power_congruence_checks']=modular
assert integer_value(3,3)%4 != integer_value(1,1)%4
result['prime_power_threshold_caution']='n >= r matters: a1 = 1 and a3 = 211 have different residues modulo 4.'

result['source_hashes_at_validation']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ROOT.iterdir()) if p.is_file() and p.suffix in ['.py','.md','.json','.txt']}
(OUT/'independent_audit_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: independent exact phase and c0-c4 symbolic checks; c0-c7 110-digit numerical checks;')
print('arbitrary vertical lines and complex-marked tail bounds; directions, moments and inverse checks.')
print('Largest coefficient discrepancy:',result['max_coefficient_difference'])
for row in contours:print('Contour:',row)
