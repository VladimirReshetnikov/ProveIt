"""Independent quadrature diagnostics; no interval-certification claim.

Run: python verification/numerical_checks.py [core|extensions|all]
Results are written after each assertion, so interrupted runs are identifiable.
"""
from __future__ import annotations
import sys,json,time,platform
from pathlib import Path
from collections import Counter
import mpmath as mp
from vertical import *

mp.mp.dps=60
mode=sys.argv[1] if len(sys.argv)>1 else 'all'
if mode not in {'core','extensions','all'}:raise SystemExit('core, extensions, or all required')
root=Path(__file__).resolve().parents[1]
records=[]
start=time.time()
tolerance=mp.mpf('1e-35')

def save():
    result={'status':'PASS' if records and all(r['passed'] for r in records) else 'INCOMPLETE_OR_FAIL',
            'mode':mode,'precision_decimal_digits':mp.mp.dps,'tolerance':str(tolerance),
            'tests':len(records),'categories':dict(Counter(r['category'] for r in records)),
            'elapsed_seconds':round(time.time()-start,2),'mpmath_version':mp.__version__,
            'python_version':platform.python_version(),
            'interpretation':'Floating-point diagnostics, not rigorous interval enclosures.',
            'records':records}
    (root/'results'/f'numerical_{mode}.json').write_text(json.dumps(result,indent=2)+'\n')

def test(name,category,lhs,rhs,tol=None):
    err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
    tol=tolerance if tol is None else tol
    passed=bool(err<tol)
    records.append({'name':name,'category':category,'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48),
                    'scaled_error':mp.nstr(err,8),'tolerance':mp.nstr(tol,5),'passed':passed})
    save()
    print(f'{len(records):02d} {"PASS" if passed else "FAIL"} {name}: {mp.nstr(err,5)}',flush=True)
    if not passed:raise AssertionError(name)

def quad(f):return mp.quad(f,[0,mp.mpf('.25'),1,4,mp.inf])
def line(f,g,a,b,p=1,q=1):
    return mp.quad(lambda y:mp.re(f(a+1j*p*y)*g(b-1j*q*y)),[0,1,10,60,mp.inf])/mp.pi

if mode in {'core','all'}:
    cases=[('0.8','1'),('1.4','1.7'),('2.4','1.2'),('3.2','2.1')]
    for ws,As in cases:
        w,A=mp.mpf(ws),mp.mpf(As)
        test(f'K at ({ws},{As})','basic_spectral',laplace_moment(w,A),mp.gamma(w)*K(w,A))
    w,A=mp.mpc('1.1','.4'),mp.mpc('1.8','.2')
    test('K with complex order and shift','basic_spectral',laplace_moment(w,A),mp.gamma(w)*K(w,A))
    for As in ['1','1.7']:
        A=mp.mpf(As)
        for n in range(5):
            lhs=(-1)**n*quad(lambda x:mp.exp(-A*x)*kernel(x)**2*bell_kernel(n,mp.log(x)))
            test(f'K derivative {n} at A={As}','spectral_jets',lhs,K_derivative_at_one(n,A))
    A=mp.mpf('1.3')
    mus=[K_derivative_at_one(j,A) for j in range(5)]
    z2,z3,z4=mp.zeta(2),mp.zeta(3),mp.zeta(4)
    table={(0,0):mus[0],(1,0):-mus[1],(1,1):mus[2]+z2*mus[0],
           (2,1):-mus[3]-2*z2*mus[1]+2*z3*mus[0],
           (3,1):mus[4]+3*z2*mus[2]-6*z3*mus[1]+6*z4*mus[0],
           (2,2):mus[4]+4*z2*mus[2]-8*z3*mus[1]+(6*z4+2*z2*z2)*mus[0]}
    for (m,n),rhs in table.items():
        lhs=quad(lambda x:mp.exp(-A*x)*kernel(x)**2*bell_kernel(m,mp.log(x))*bell_kernel(n,mp.log(x)))
        test(f'Stieltjes pairing ({m},{n})','mixed_stieltjes_jets',lhs,rhs)
    z=mp.mpc('.8','.6')
    cauchy_values=stieltjes_cauchy(2,z)
    for n in range(3):
        lhs=quad(lambda x:mp.exp(-z*x)*kernel(x)*bell_kernel(n,mp.log(x)))
        rhs=cauchy_values[n]
        test(f'complex G_{n} Laplace representation','pointwise_stieltjes',lhs,rhs)
    for a,b in [(mp.mpf('.5'),mp.mpf('.5')),(mp.mpf('.3'),mp.mpf('1.4'))]:
        test(f'direct G0 line a={a},b={b}','direct_vertical',line(G0,G0,a,b),K_one(a+b))
        test(f'direct Omega line a={a},b={b}','direct_vertical',line(Omega,Omega,a,b),omega_pair(a+b))
    for p,q in [(1,2),(2,3)]:
        a,b=mp.mpf('.5'),mp.mpf('.5')
        test(f'direct G0 slopes ({p},{q})','direct_vertical',line(G0,G0,a,b,p,q),K_pq_one(q*a+p*b,p,q))
    rhs=mp.loggamma(mp.mpf('.25'))-mp.log(mp.pi)/2-mp.log(2)/4+3*mp.log(3)/4-mp.mpf('.75')-mp.pi/8
    test('quarter-Gamma scale-(1,2) reduction','special_values',K_pq_one(mp.mpf('1.5'),1,2),rhs)
    test('Stirling squared norm at half shift','special_values',omega_pair(mp.mpf(1)),
         mp.zeta(-1,derivative=1)+mp.zeta(3)/(2*mp.pi**2)+mp.mpf(1)/9)
    for r,t in [(1,1),(1,2),(2,2)]:
        a,b=mp.mpf('.7'),mp.mpf('.6');A=a+b
        rhs=(-1)**(r+t)*mp.factorial(r+t)*(mp.zeta(r+t,A)+(1-A)*mp.zeta(r+t+1,A))
        test(f'direct polygamma ({r},{t})','direct_vertical',
             line(lambda z:mp.polygamma(r,z),lambda z:mp.polygamma(t,z),a,b),rhs)

if mode in {'extensions','all'}:
    A=mp.mpf('2.3')
    for d,e,p,q,ws in [(0,1,2,3,'.4'),(1,1,1,2,'-.7'),(2,1,2,1,'-2.3'),
                       (2,2,2,3,'-3.4'),(3,0,1,2,'-1.3'),(3,2,2,1,'-5.2')]:
        w=mp.mpf(ws)
        test(f'compensated ({d},{e}), slopes ({p},{q}), w={ws}','compensated_spectral',
             laplace_moment(w,A,d,e,p,q),J_formula(w,A,d,e,p,q))
    for d,e,p,q,w in [(0,0,1,1,1),(0,0,2,3,2),(1,0,1,2,0),
                       (1,1,1,1,-1),(2,2,1,2,-4),(2,2,2,3,-5)]:
        val,res=J_at_integer(w,A,d,e,p,q)
        test(f'integer finite value d={d},e={e},p={p},q={q},w={w}',
             'removable_integer_values',laplace_moment(w,A,d,e,p,q),val)
        test(f'numeric residue d={d},e={e},p={p},q={q},w={w}',
             'removable_residues',res,mp.mpf(0))
    z=mp.mpc('1.2','.4')
    for d,n in [(2,1),(2,2),(3,3),(3,4)]:
        lhs=(-1)**n*quad(lambda x:x**(-n-1)*mp.exp(-z*x)*kernel(x,d))
        test(f'normalized primitive depth={d},n={n}','primitives',lhs,primitive(d,n,z))
    test('primitive differential ladder','primitives',mp.diff(lambda z:primitive(2,2,z),z),primitive(2,1,z))
    # Colored Lerch product: independent kernel integral versus partial fractions.
    for xi,eta,ws,As in [(mp.mpf('.3'),mp.mpf('-.6'),'1.3','1.7'),
                         (mp.mpc('.2','.4'),mp.mpc('-.3','.2'),'1.2','1.1'),
                         (mp.mpf('-.4'),mp.mpf('-.4'),'1.4','1.3')]:
        w,A=mp.mpf(ws),mp.mpf(As)
        lhs=quad(lambda x:x**(w-1)*mp.exp(-A*x)/((1-xi*mp.exp(-x))*(1-eta*mp.exp(-x))))
        rhs=mp.gamma(w)*((xi*mp.lerchphi(xi,w,A)-eta*mp.lerchphi(eta,w,A))/(xi-eta)
                       if xi!=eta else mp.lerchphi(xi,w-1,A)+(1-A)*mp.lerchphi(xi,w,A))
        test(f'Lerch colors {xi},{eta}','lerch_products',lhs,rhs)
    w,xi,eta=mp.mpf('1.4'),mp.mpf('.3'),mp.mpf('-.6')
    lhs=quad(lambda x:x**(w-1)*mp.exp(-x)/((1-xi*mp.exp(-x))*(1-eta*mp.exp(-x))))
    test('polylogarithm divided difference','lerch_products',lhs,
         mp.gamma(w)*(mp.polylog(w,xi)-mp.polylog(w,eta))/(xi-eta))
    for xi in [mp.mpf('.3'),mp.mpf(-1)]:
        w,A=mp.mpf('1.7'),mp.mpf('1.3')
        lhs=quad(lambda x:x**(w-1)*mp.exp(-A*x)*kernel(x)/(1-xi*mp.exp(-x)))
        rhs=mp.gamma(w)*((mp.zeta(w,A)-xi*mp.lerchphi(xi,w,A))/(1-xi)
                         -mp.lerchphi(xi,w-1,A)/(w-1))
        test(f'mixed Stieltjes-Lerch xi={xi}','mixed_lerch',lhs,rhs)
        lhs=quad(lambda x:mp.exp(-x)*kernel(x)/(1-xi*mp.exp(-x)))
        rhs=(mp.euler+mp.log(1-xi))/(1-xi)-mp.diff(lambda s:mp.polylog(s,xi),0)/xi
        test(f'mixed resonance xi={xi}','mixed_lerch',lhs,rhs)
    lhs=quad(lambda x:mp.exp(-x)*kernel(x)/(1+mp.exp(-x)))
    test('alternating mixed special value','special_values',lhs,mp.euler/2+mp.log(2)-mp.log(mp.pi)/2)
    for q in [3,4]:
        xi=mp.exp(2j*mp.pi/q);A=mp.mpf('1.3')
        lhs=mp.diff(lambda s:mp.lerchphi(xi,s,A),0)
        rhs=mp.fsum(xi**r*(mp.zeta(0,(A+r)/q,derivative=1)
                          -mp.log(q)*mp.zeta(0,(A+r)/q)) for r in range(q))
        test(f'root-of-unity Gamma reduction q={q}','root_of_unity',lhs,rhs)
    for M,N in [(2,3),(3,4)]:
        w,A=mp.mpf('1.3'),mp.mpf('1.4')
        lhs=quad(lambda x:x**(w-1)*mp.exp(-A*x)*mp.fsum(mp.exp(-j*x) for j in range(M))
                 *mp.fsum(mp.exp(-k*x) for k in range(N)))
        rhs=mp.gamma(w)*mp.fsum((A+j+k)**(-w) for j in range(M) for k in range(N))
        test(f'finite harmonic ({M},{N})','finite_harmonic',lhs,rhs)
    A,w,N=mp.mpf('1.4'),mp.mpf('1.3'),4
    lhs=quad(lambda x:x**(w-1)*mp.exp(-A*x)*kernel(x)*mp.fsum(mp.exp(-j*x) for j in range(N)))
    rhs=mp.gamma(w)*mp.fsum(mp.zeta(w,A+j)-(A+j)**(1-w)/(w-1) for j in range(N))
    test('mixed finite-harmonic closure','finite_harmonic',lhs,rhs)

save()
print(f'Completed {len(records)} tests in {time.time()-start:.1f}s.',flush=True)
