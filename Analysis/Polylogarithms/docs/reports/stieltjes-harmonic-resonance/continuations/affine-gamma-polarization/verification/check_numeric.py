#!/usr/bin/env python3
"""Floating-point diagnostics, NOT rigorous interval enclosures.
Run separately with --part kernel|transform|stieltjes|extras, or all.
"""
import argparse, json
from pathlib import Path
from math import comb
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(); p.add_argument('--dps',type=int,default=50)
p.add_argument('--part',choices=['kernel','transform','stieltjes','extras','all'],default='all')
args=p.parse_args()
if args.dps<35: raise ValueError('Use at least 35 working decimal digits.')
mp.mp.dps=args.dps; rows=[]
tol=mp.mpf(10)**(-min(30,args.dps-15))

def check(label,lhs,rhs,tolerance=None):
    err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
    lim=tol if tolerance is None else tolerance
    if not mp.isfinite(err) or err>lim:
        raise ArithmeticError(f'{label}: scaled residual {mp.nstr(err,12)} > {lim}')
    rows.append({'test':label,'lhs':mp.nstr(lhs,42),'rhs':mp.nstr(rhs,42),
                 'scaled_residual':mp.nstr(err,8),'threshold':mp.nstr(lim,8)})
    print(label,mp.nstr(err,5),flush=True)

def gr(r,y):
    return (-1)**r/mp.factorial(2*r+2)*mp.hyp0f1(r+mp.mpf('1.5'),y*y/4)

def cr(r):
    return mp.mpf((-1)**r)/(2**(2*r+1)*mp.factorial(r)*mp.factorial(r+1))

def compact(r,s,a,b):
    return cr(r)/2*mp.quad(lambda v:(1-v*v)**r*mp.zeta(s,a+b*v),[-1,0,1])

def endpoint(r,s,a,b,z=1):
    def phi(ss,x):
        return mp.zeta(ss,x) if z==1 else mp.lerchphi(z,ss,x)
    return mp.fsum(mp.mpf((-1)**j)*mp.factorial(j)*comb(r,j-r)/
         (2**(j+2)*mp.factorial(r)*mp.factorial(r+1)*b**(j+1))*
         (phi(s-j-1,a+b)-(-1)**j*phi(s-j-1,a-b))/mp.rf(1-s,j+1)
         for j in range(r,2*r+1))

def mellin(r,s,a,b,z=1):
    # -expm1(-t) prevents cancellation at the origin when z=1.
    return mp.quad(lambda t:t**(s-1)*mp.exp(-a*t)*gr(r,b*t)/
                   (-mp.expm1(-t) if z==1 else 1-z*mp.exp(-t)),
                   [0,1,4,12,mp.inf])/mp.gamma(s)

def homogeneous(j,m):
    hs=[mp.mpf(1)]
    for n in range(1,m+1):
        hs.append(mp.fsum(mp.fsum(mp.mpf(k)**(-l) for k in range(1,j+1))*hs[n-l] for l in range(1,n+1))/n)
    return hs

def stieltjes_endpoint(r,m,a,b):
    total=mp.mpf('0')
    for j in range(r,2*r+1):
        D=mp.mpf((-1)**j*comb(r,j-r))/(2**(j+2)*mp.factorial(r)*mp.factorial(r+1)*b**(j+1))
        hs=homogeneous(j,m+1)
        for k in range(m+2):
            F=mp.diff(lambda ss:mp.zeta(ss,a+b)-(-1)**j*mp.zeta(ss,a-b),-j,k)
            total+=D*hs[m+1-k]*F/mp.factorial(k)
    return (-1)**(m+1)*mp.factorial(m)*total

if args.part in ('kernel','all'):
    for r in [2,3,4,6,9]:
        for y in [mp.mpf('0'),mp.mpf('.8'),mp.mpc('.6','.3')]:
            check(f'beta kernel r={r},y={y}',gr(r,y),
                  cr(r)*mp.quad(lambda v:(1-v*v)**r*mp.cosh(y*v),[0,1]))

if args.part in ('transform','all'):
    for r,s,a,b in [(2,mp.mpf('2.4'),mp.mpf(2),mp.mpf(1)),
                     (3,mp.mpf('1.6'),mp.mpf('2.25'),mp.mpf('.5')),
                     (5,mp.mpf('3.3'),mp.mpf('1.5'),mp.mpf('.25')),
                     (2,mp.mpc('1.7','.3'),mp.mpf(2),mp.mpf('.75'))]:
        c=compact(r,s,a,b)
        check(f'Hurwitz endpoints r={r},s={s}',c,endpoint(r,s,a,b))
        check(f'Mellin kernel r={r},s={s}',mellin(r,s,a,b),c)
    W=lambda x:(x-1)**2*(3-x)**2
    zp=lambda s:mp.diff(mp.zeta,s)
    values=[mp.mpf(83)/180-8*zp(-3),6*mp.zeta(3)/mp.pi**2,
            -48*zp(-1)+8*mp.log(2)-14,24*mp.log(4*mp.pi)-60,
            48*mp.euler+24*mp.log(2)-46,84-8*mp.pi**2]
    for order,val in enumerate(values):
        check(f'quartic-weight polygamma order={order}',
              mp.quad(lambda x:W(x)*mp.polygamma(order,x),[1,2,3]),val)

if args.part in ('stieltjes','all'):
    for r,a,b in [(2,mp.mpf(2),mp.mpf(1)),(3,mp.mpf('1.5'),mp.mpf('.25'))]:
        lhs=-cr(r)/2*mp.quad(lambda v:(1-v*v)**r*mp.digamma(a+b*v),[-1,0,1])
        check(f'Stieltjes gamma0 r={r}',lhs,stieltjes_endpoint(r,0,a,b))
    r=2; a=mp.mpf(2); b=mp.mpf(1)
    def gamma1_gauss(n):
        nodes,weights=mp.gauss_quadrature(n,'legendre')
        return cr(r)/2*mp.fsum(weights[i]*(1-nodes[i]**2)**r*mp.stieltjes(1,a+b*nodes[i]) for i in range(n))
    coarse=gamma1_gauss(24); fine=gamma1_gauss(36)
    check('Stieltjes gamma1 quadrature convergence',coarse,fine,mp.mpf('1e-23'))
    check('Stieltjes gamma1 endpoints',fine,stieltjes_endpoint(r,1,a,b),mp.mpf('1e-29'))
    closed=mp.mpf(367)/432-mp.mpf(4)/3*mp.log(2)-mp.mpf(44)/3*mp.diff(mp.zeta,-3)-4*mp.diff(mp.zeta,-3,2)
    check('quartic gamma1 explicit zeta jet',768*fine,closed,mp.mpf('1e-29'))
    a0=mp.mpf('1.7'); a1=mp.mpf('2.4'); b=mp.mpf('.4'); r=3
    primitive=-cr(r)/2*mp.quad(lambda v:(1-v*v)**r*(mp.loggamma(a1+b*v)-mp.loggamma(a0+b*v)),[-1,0,1])
    # Integrate the finite endpoint formula, independently of the log-Gamma representation.
    # A Gauss rule avoids nested adaptive spectral differentiation.
    nodes,weights=mp.gauss_quadrature(24,'legendre')
    lhs=(a1-a0)/2*mp.fsum(weights[i]*stieltjes_endpoint(r,0,(a1+a0)/2+(a1-a0)*nodes[i]/2,b) for i in range(24))
    check('anchored gamma0 primitive',lhs,primitive,mp.mpf('1e-29'))

if args.part in ('extras','all'):
    z=mp.mpf('.3'); s=mp.mpf('2.7')
    check('Lerch deformation',mellin(2,s,mp.mpf(2),mp.mpf(1),z),
          endpoint(2,s,mp.mpf(2),mp.mpf(1),z))
    for N in [1,2,3,5]:
        rhs=z**(-N)*(mp.polylog(s,z)-mp.fsum(z**k/k**s for k in range(1,N)))
        check(f'polylogarithm integer endpoint N={N}',mp.lerchphi(z,s,N),rhs)
    for A,q in [(1,3),(4,3),(7,4)]:
        w=z**(mp.mpf(1)/q); omega=mp.exp(2j*mp.pi/q)
        rhs=q**(s-1)*w**(-A)*mp.fsum(omega**(-l*A)*mp.polylog(s,w*omega**l) for l in range(q))
        rhs-=q**s*w**(-A)*mp.fsum(w**k/k**s for k in range(1,A) if (k-A)%q==0)
        check(f'cyclotomic endpoint A={A},q={q}',mp.lerchphi(z,s,mp.mpf(A)/q),rhs)
    M=lambda t:(t*t+3)*mp.sinh(t)-3*t*mp.cosh(t)
    J=mp.quad(lambda t:48*t**5*mp.exp(-2*t)*gr(2,t)/(1-z*mp.exp(-t)),[0,1,4,12,mp.inf])
    Jclosed=4/z**2+mp.mpf(5)/(4*z)-(1-z*z)/z**3*(mp.polylog(3,z)+mp.mpf('1.5')*mp.polylog(1,z))-mp.mpf('1.5')*(1+z*z)/z**3*mp.polylog(2,z)
    check('three-polylogarithm hyperbolic integral',J,Jclosed)
    for r in range(2,7):
        ss=mp.mpf('2.4') if r!=4 else mp.mpc('2.4','.2')
        lhs=mp.quad(lambda x:(mp.bernpoly(2*r,(x-1)/2)-mp.bernoulli(2*r))*mp.zeta(ss,x),[1,2,3])
        rhs=-mp.factorial(2*r)*mp.zeta(ss-2*r)/(2**(2*r-1)*mp.rf(1-ss,2*r))
        for j in range(2,2*r+1):
            d=mp.factorial(2*r)*mp.bernpoly(2*r-j,1)/(2**j*mp.factorial(2*r-j))
            rhs-=(-1)**j*d*(1+2**(j+1-ss))/mp.rf(1-ss,j+1)
        check(f'full complex-order Bernoulli selector r={r}',lhs,rhs)
    constants=json.loads((ROOT/'data/bernoulli_trigamma_constants.json').read_text())
    for item in constants[:7]:
        r=item['r']
        lhs=mp.quad(lambda x:(mp.bernpoly(2*r,(x-1)/2)-mp.bernoulli(2*r))*mp.polygamma(1,x),[1,2,3])
        R=mp.mpf(item['rational'])
        rhs=R+(-1)**r*mp.factorial(2*r)/(2**(4*r-2)*mp.pi**(2*r-2))*mp.zeta(2*r-1)
        check(f'Bernoulli single-zeta r={r}',lhs,rhs)

result={'status':'PASS','part':args.part,'working_decimal_digits':args.dps,'comparisons':len(rows),
        'default_scaled_threshold':mp.nstr(tol,5),
        'largest_scaled_residual':mp.nstr(max(mp.mpf(x['scaled_residual']) for x in rows),10),
        'scope':'Floating-point diagnostics, not certified enclosures and not proofs.', 'tests':rows}
(ROOT/f'data/numeric_{args.part}_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='tests'},indent=2),flush=True)
