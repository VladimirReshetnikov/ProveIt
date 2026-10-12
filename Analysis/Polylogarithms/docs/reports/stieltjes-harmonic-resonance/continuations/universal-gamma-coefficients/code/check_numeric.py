"""High-precision diagnostics, not rigorous interval certificates."""
from pathlib import Path
from fractions import Fraction
from math import factorial, comb
import json, time
import mpmath as mp
from mixed_coefficients import r
from normal_forms import hierarchy
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=60
records=[]

def number(x):
    return mp.mpf(x.numerator)/x.denominator

def check(name,left,right,tol=mp.mpf('1e-48')):
    err=abs(left-right)/max(mp.mpf(1),abs(left),abs(right))
    assert err<tol,(name,mp.nstr(left,25),mp.nstr(right,25),mp.nstr(err,8))
    records.append({'name':name,'scaled_residual':mp.nstr(err,8)})

def kernel(v,b,c):
    return -(v**(c-2)*(1-v*v)**3*(1+3*v*v)**b*(1+v*v)**(c-2))/(4*factorial(b)*factorial(c)*24**b*48**c)

def G(s,a,z):
    A=mp.polylog(1,z)-mp.fsum(z**j/j for j in range(1,a+1))
    if s==0:return z**(-a)*A
    return mp.fsum((-1)**(s-j)*mp.polylog(j,z)/mp.mpf(a)**(s-j+1) for j in range(1,s+1))+(-1)**s/mp.mpf(a)**s*z**(-a)*A

def kernel_terms(b,c):
    # Expand the polynomial density with exact coefficients.
    terms={}
    den=4*factorial(b)*factorial(c)*24**b*48**c
    for i in range(4):
      for j in range(b+1):
       for l in range(c-1):
        a=c-1+2*(i+j+l)
        terms[a]=terms.get(a,Fraction(0))-Fraction((-1)**i*comb(3,i)*comb(b,j)*3**j*comb(c-2,l),den)
    return terms

def poly(P,u):
    return mp.fsum(number(c)*mp.fprod(u[j]**a for j,a in enumerate(mon) if a) for mon,c in P.items())

def main():
    start=time.perf_counter()
    for c in range(2,6):
      for b in range(4):
       for k in [c%2,c%2+4]:
        q=mp.quad(lambda v:v**k*kernel(v,b,c),[0,mp.mpf('.5'),1])
        check(f'beta b={b} c={c} k={k}',number(r(k,b,c)),q)
    for b in [2,3,5]:
      for k in [0,2,6]:
        q=3/mp.mpf(factorial(b)*24**b)*mp.quad(lambda v:v**k*(1-v*v)**2*(1+3*v*v)**(b-2),[0,1])
        check(f'two-jet beta b={b} k={k}',number(r(k,b,0)),q)
    for b,c in [(1,2),(2,2),(0,3),(1,4)]:
      for s in [0,1,3]:
        z=mp.mpc('.35','.2')
        direct=mp.fsum(number(r(k,b,c))*z**k/mp.mpf(k)**s for k in range(1,350) if (k+c)%2==0)
        closed=mp.fsum(number(d)*(G(s,a,z)+(-1)**c*G(s,a,-z))/2 for a,d in kernel_terms(b,c).items())
        check(f'polylog b={b} c={c} s={s}',direct,closed)
    P=lambda v:(1-v*v)**3*(1+3*v*v)/192
    check('rational endpoint',mp.quad(lambda v:(1-v*v)**2*(1+3*v*v)/192,[0,1]),mp.mpf(1)/252)
    for s in [1,2]:
        def integrand(v):
            if v==1:return mp.mpf(0)
            return ((1-v)**2*(1+v)**3*(1+3*v*v)*mp.polylog(s,v)+(1+v)**2*(1-v)**3*(1+3*v*v)*mp.polylog(s,-v))/384
        value=mp.quad(integrand,[0,mp.mpf('.5'),1])
        exact=(mp.mpf(299)/70560-mp.log(2)/252) if s==1 else (-mp.mpf(66161)/11113200+mp.mpf(275)*mp.pi**2/774144+mp.mpf(67)*mp.log(2)/13230)
        check(f'harmonic endpoint H^(s), s={s}',value,exact)
        z=mp.mpf('.65'); H=mp.mpf(0); direct=mp.mpf(0)
        for k in range(1,500):
            H+=1/mp.mpf(k)**s
            if k%2==0:direct+=H*z**k/((k+1)*(k+5)*(k+7)*(k+9))
        value=mp.quad(lambda v:P(v)*(mp.polylog(s,z*v)/(1-z*v)+mp.polylog(s,-z*v)/(1+z*v))/2,[0,1])
        check(f'harmonic damped direct series s={s}',direct,value)
    polynomials={m:(A,N,H) for m,A,N,H in hierarchy(14)}
    for m in [4,8,11,14]:
        _,N,H=polynomials[m]; Aprev=polynomials[m-1][0]
        def at(x):return [mp.polygamma(j,x) for j in range(m)]
        def integrand(x):
            u=at(x);return (poly(N,u)+u[0]*poly(H,u))/mp.gamma(x)
        def primitive(x):
            u=at(x);return -(poly(Aprev,u)+poly(H,u))/mp.gamma(x)
        lo=mp.mpf('1.1');hi=mp.mpf('1.3')
        check(f'Gamma weighted primitive m={m}',mp.quad(integrand,[lo,hi]),primitive(hi)-primitive(lo))
    # Order derivatives at s=0 and the independent Hurwitz Laurent coefficient.
    for q in range(3):
        a=mp.mpf('1.25')
        d=mp.diff(lambda t:mp.diff(lambda s:mp.zeta(s,t),0,q+1),a)
        left=(-1)**q*d/(q+1)
        check(f'Stieltjes primitive q={q}',left,-mp.stieltjes(q,a),mp.mpf('1e-42'))
    report={'result':'PASS','working_decimal_digits':60,'number_of_diagnostics':len(records),
            'maximum_scaled_residual':mp.nstr(max(mp.mpf(x['scaled_residual']) for x in records),8),
            'elapsed_seconds':time.perf_counter()-start,'checks':records,
            'scope':'Floating-point diagnostics only; not interval enclosures or proofs.'}
    (ROOT/'data'/'numeric_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
