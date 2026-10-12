"""Exact endpoint algebra and independent high-precision analytic diagnostics.

Requires mpmath and sympy. These are numerical diagnostics, not interval proofs.
The script writes individual residuals and explicit local tolerances.
"""
from __future__ import annotations
import argparse, json, platform
from pathlib import Path
from math import factorial
import mpmath as mp
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'data')
    parser.add_argument('--dps',type=int,default=65)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=args.dps
    v=sp.symbols('v');P=sp.expand((1-v*v)**3*(1+3*v*v))
    derivatives={j:sp.diff(P,v,j).subs(v,1) for j in range(3,9)}
    c={j:(-1)**j*derivatives[j]/sp.factorial(j) for j in derivatives}
    assert sp.integrate(P,(v,-1,1))==sp.Rational(128,105)
    assert [c[j] for j in range(3,9)]==[32,-96,120,-76,24,-3]
    exact_count=2
    # Finite endpoint identity for all nonpositive integral orders in a grid.
    A,B=sp.Rational(7,3),sp.Rational(2,5)
    for n in range(0,13):
        s=-n
        left=sp.integrate(P*(-sp.bernoulli(n+1,A+B*v)/(n+1)),(v,-1,1))
        right=0
        for j,d in derivatives.items():
            zp=lambda x:-sp.bernoulli(n+j+2,x)/(n+j+2)
            right+=(-1)**j*d*(zp(A+B)-(-1)**j*zp(A-B))/(B**(j+1)*sp.rf(1-s,j+1))
        assert sp.simplify(left-right)==0
        exact_count+=1
    L=sp.Symbol('L');g0=g1=res=sp.S(0)
    for j in derivatives:
        B0=(1-(-1)**j)*sp.zeta(-j)-1-2**j
        B1=(1-(-1)**j)*sp.Symbol('Zp'+str(j))+2**j*L
        B2=(1-(-1)**j)*sp.Symbol('Zpp'+str(j))/2-2**j*L**2/2
        H=sp.harmonic(j);h2=(H**2+sp.harmonic(j,2))/2
        res-=c[j]*B0;g0-=c[j]*(B1+H*B0);g1+=c[j]*(B2+H*B1+h2*B0)
    assert sp.simplify(res-sp.Rational(128,105))==0;exact_count+=1
    expected0=-64*sp.Symbol('Zp3')-240*sp.Symbol('Zp5')-48*sp.Symbol('Zp7')-sp.Rational(547,1800)
    expected1=(sp.Rational(3499687,10584000)-sp.Rational(32,21)*L+
               sp.Rational(352,3)*sp.Symbol('Zp3')+548*sp.Symbol('Zp5')+
               sp.Rational(4356,35)*sp.Symbol('Zp7')+32*sp.Symbol('Zpp3')+
               120*sp.Symbol('Zpp5')+24*sp.Symbol('Zpp7'))
    assert sp.expand(g0-expected0)==0;assert sp.expand(g1-expected1)==0;exact_count+=2
    # Pole and elementary part at s=2, independent from the numerical comparison.
    rat=tres=sp.S(0)
    for j,d in derivatives.items():
        E0=(1-(-1)**j)*sp.zeta(1-j)-1-2**(j-1)
        coef=(-1)**j*d/sp.factorial(j-1)
        tres+=coef*E0
        rat+=coef*(2**(j-1)*L+(sp.harmonic(j-1)-1)*E0)
    assert sp.simplify(tres)==0;assert sp.simplify(rat+sp.Rational(32,35))==0;exact_count+=2
    dm={j:mp.mpf(int(d)) for j,d in derivatives.items()}
    p=lambda x:(1-x*x)**3*(1+3*x*x)
    results=[]
    def check(name,left,right,tolerance='1e-40'):
        err=abs(left-right)/(1+abs(left)+abs(right));tol=mp.mpf(tolerance)
        if not err<tol:raise AssertionError((name,mp.nstr(err,20),tolerance))
        results.append({'name':name,'left':mp.nstr(left,48),'right':mp.nstr(right,48),
                        'scaled_residual':mp.nstr(err,12),'tolerance':tolerance})
        print('PASS',name,mp.nstr(err,5),flush=True)
    def endpoint(s,A,B,xi=None):
        if xi is None:Z=lambda s,a:mp.zeta(s,a)
        else:Z=lambda s,a:mp.lerchphi(xi,s,a)
        return mp.fsum([(-1)**j*d/(B**(j+1)*mp.rf(1-s,j+1))*
                        (Z(s-j-1,A+B)-(-1)**j*Z(s-j-1,A-B)) for j,d in dm.items()])
    for idx,(s,A,B) in enumerate([(mp.mpf('2.4'),mp.mpf('2.3'),mp.mpf('.7')),
                                 (mp.mpc('1.3','.4'),mp.mpf('2'),mp.mpf('1')),
                                 (mp.mpf('-.6'),mp.mpf('1.8'),mp.mpf('.5'))]):
        left=mp.quad(lambda x:p(x)*mp.zeta(s,A+B*x),[-1,0,1])
        check('Hurwitz finite endpoints '+str(idx),left,endpoint(s,A,B))
    # Trigamma and generalized Stieltjes evaluations for the degree-eight weight.
    zp={j:mp.diff(mp.zeta,-j) for j in [3,5,7]}
    zpp={j:mp.diff(mp.zeta,-j,2) for j in [3,5,7]}
    trig=(-48*mp.zeta(3)/mp.pi**2+900*mp.zeta(5)/mp.pi**4-
          1890*mp.zeta(7)/mp.pi**6-mp.mpf(32)/35)
    check('weighted trigamma',mp.quad(lambda x:p(x)*mp.polygamma(1,2+x),[-1,0,1]),trig)
    g0val=-64*zp[3]-240*zp[5]-48*zp[7]-mp.mpf(547)/1800
    check('weighted gamma_0',mp.quad(lambda x:-p(x)*mp.digamma(2+x),[-1,0,1]),g0val)
    g1val=(mp.mpf(3499687)/10584000-mp.mpf(32)/21*mp.log(2)+
           mp.mpf(352)/3*zp[3]+548*zp[5]+mp.mpf(4356)/35*zp[7]+
           32*zpp[3]+120*zpp[5]+24*zpp[7])
    def gauss_stieltjes(n):
        nodes,weights=mp.gauss_quadrature(n,'legendre')
        return mp.fsum(weights[k]*p(nodes[k])*mp.stieltjes(1,2+nodes[k]) for k in range(n))
    g1_32=gauss_stieltjes(32);g1_48=gauss_stieltjes(48)
    check('gamma_1 quadrature refinement 32/48',g1_32,g1_48,'1e-31')
    check('weighted gamma_1 endpoint value',g1_48,g1val,'1e-40')
    # An ordinary log-sine integral (the imaginary Li_1 part cancels by parity).
    logsine=-24*mp.zeta(5)/mp.pi**4+450*mp.zeta(7)/mp.pi**6-945*mp.zeta(9)/mp.pi**8
    left=2*mp.quad(lambda x:p(x)*mp.log(2*mp.sin(mp.pi*x)),[0,mp.mpf('.5'),1])
    check('weighted log-sine',left,logsine)
    # Polylogarithm endpoint identity on a compact interval, distinct from Fourier identity.
    xi=mp.mpf('.35');s=mp.mpf('1.6')
    # Use a normally convergent defining series, rather than repeated Lerch calls in quadrature.
    nodes,weights=mp.gauss_quadrature(48,'legendre')
    def lerch_series(a):
        return mp.fsum(xi**n/(n+a)**s for n in range(170))
    left=mp.fsum(weights[k]*p(nodes[k])*lerch_series(2+nodes[k]) for k in range(48))
    def integer_lerch(s,N):
        return (mp.polylog(s,xi)-mp.fsum(xi**n/n**s for n in range(1,N)))/xi**N
    right=mp.fsum((-1)**j*d/mp.rf(1-s,j+1)*
                 (integer_lerch(s-j-1,3)-(-1)**j*integer_lerch(s-j-1,1)) for j,d in dm.items())
    check('finite polylogarithmic endpoints',left,right,'1e-40')
    # Polynomial-background beta kernels and their mixed finite coefficients.
    for r,b,k in [(3,1,0),(3,2,2),(4,3,4),(5,2,1),(6,4,0)]:
        left=mp.quad(lambda x:x**k*(1-x*x)**r*(1+3*x*x)**b,[0,1])
        right=2**r*factorial(r)*mp.fsum(mp.binomial(b,j)*3**j/
                mp.fprod(k+2*j+2*l+1 for l in range(r+1)) for j in range(b+1))
        check('mixed beta moment '+str((r,b,k)),left,right)
    # All logarithmic orders of a mixed beta moment, checked at a nonintegral exponent.
    r,b,k=3,2,mp.mpf('.7')
    def J(q):
        return 2**r*factorial(r)*mp.fsum(mp.binomial(b,j)*3**j/
               mp.fprod(q+2*j+2*l+1 for l in range(r+1)) for j in range(b+1))
    for order in range(1,5):
        left=mp.quad(lambda x:x**k*(1-x*x)**r*(1+3*x*x)**b*(-mp.log(x))**order,[0,1])
        check('logarithmic beta moment '+str(order),left,(-1)**order*mp.diff(J,k,order))
    # Anchored first Stieltjes primitive: compare Gamma endpoints and a nested integral.
    A0,A1=mp.mpf('2'),mp.mpf('2.4');B=mp.mpf('.6')
    primitive=-mp.quad(lambda x:p(x)*(mp.loggamma(A1+B*x)-mp.loggamma(A0+B*x)),[-1,0,1])
    # Integrate the digamma primitive in A by independent Gaussian quadrature.
    an,aw=mp.gauss_quadrature(24,'legendre');vn,vw=mp.gauss_quadrature(32,'legendre')
    direct=mp.fsum(aw[i]*vw[j]*p(vn[j])*(-mp.digamma((A0+A1)/2+(A1-A0)*an[i]/2+B*vn[j]))
                   for i in range(24) for j in range(32))*(A1-A0)/2
    check('anchored gamma_0 primitive',direct,primitive,'1e-38')
    # An exact Gamma differential identity after ordinary integration, with its endpoint retained.
    from independent_ibp import hierarchy,norm,prim
    A8=list(hierarchy(8))[-1];N8=norm(A8);H8=prim(A8)
    def evaluate(poly,x):
        n=max((len(e) for e in poly),default=0)
        jets=[mp.digamma(x)]+[mp.polygamma(j,x) for j in range(1,n)]
        return mp.fsum(mp.mpf(c.numerator)/c.denominator*mp.fprod(jets[j]**e[j] for j in range(len(e)))
                       for e,c in poly.items())
    alpha,beta=mp.mpf('1.2'),mp.mpf('1.8')
    left=mp.quad(lambda x:evaluate(A8,x)-evaluate(N8,x),[alpha,beta])
    check('Gamma weight-eight retained endpoint',left,evaluate(H8,beta)-evaluate(H8,alpha),'1e-40')
    out={'status':'PASS','working_decimal_digits':args.dps,'exact_endpoint_assertions':exact_count,
         'numerical_diagnostics':len(results),'results':results,
         'environment':{'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__},
         'scope':'Floating-point diagnostics with local tolerances; not rigorous interval enclosures.'}
    (args.output/'analytic_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    (args.output/'degree_eight_endpoints.json').write_text(json.dumps({
        'polynomial':str(P),'mass':'128/105','endpoint_derivatives':{str(j):str(d) for j,d in derivatives.items()},
        'stieltjes_coefficients':{str(j):str(d) for j,d in c.items()},
        'gamma0_symbolic':str(sp.expand(g0)),'gamma1_symbolic':str(sp.expand(g1))},indent=2)+'\n')
    print('ALL PASS',len(results),'diagnostics',exact_count,'exact endpoint assertions',flush=True)

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Verification requires assertions; do not use python -O.')
    main()
