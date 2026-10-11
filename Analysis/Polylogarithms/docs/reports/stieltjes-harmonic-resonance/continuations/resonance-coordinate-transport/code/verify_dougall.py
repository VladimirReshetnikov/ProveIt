"""Independent finite-sum checks for centered Dougall resonance formulas.

Numerical tail completion uses a finite Stirling expansion; it is a regression
check, not a rigorous enclosure and not part of the proof.
"""
import json
from pathlib import Path

import mpmath as mp
import sympy as sp

mp.mp.dps = 75


def coefficients(a, b, c, u, count):
    d0 = 1 + a - b - c
    shifts = [a / 2, b - a / 2, c - a / 2, d0 - u - a / 2]
    h = [mp.mpf(0)] + [
        -sum(mp.bernpoly(2 * k + 1, v) for v in shifts) / (k * (2 * k + 1))
        for k in range(1, count)
    ]
    C = [mp.mpf(1)]
    for j in range(1, count):
        C.append(sum(k * h[k] * C[j-k] for k in range(1, j+1)) / j)
    return C


def r(n, a, b, c, u):
    d0 = 1 + a - b - c
    return ((n+a/2)*mp.gamma(n+a)*mp.gamma(n+b)*mp.gamma(n+c)
            *mp.gamma(n+d0-u)*mp.rgamma(n+1)*mp.rgamma(n+1+a-b)
            *mp.rgamma(n+1+a-c)*mp.rgamma(n+b+c+u))


def completed_series(a, b, c, u, K, cutoff=120, terms=12):
    eta = a/2
    C = coefficients(a,b,c,u,terms)
    main = mp.fsum(r(n,a,b,c,u)-mp.fsum(C[j]*(n+eta)**(-1-2*u-2*j)
                                      for j in range(K))
                   for n in range(cutoff))
    tail = mp.fsum(C[j]*mp.zeta(1+2*u+2*j,cutoff+eta)
                   for j in range(K,terms))
    return main+tail


def analytic_E(a,b,c,N,t):
    d0=1+a-b-c
    return (mp.gamma(b)*mp.gamma(c)*mp.gamma(d0+N-t)*mp.gamma(1+t)
            *mp.rgamma(d0)*mp.rgamma(b+t)*mp.rgamma(c+t)
            *mp.fprod((b+t-j)*(c+t-j)/(t-j) for j in range(1,N+1)))


def jet_formula(a,b,c,N,m,K=None):
    if K is None:
        K=N+1
    eta=a/2
    cj=lambda j,q: mp.diff(lambda t: coefficients(a,b,c,-N+t,K)[j],0,q)/mp.factorial(q)
    e=mp.diff(lambda t:analytic_E(a,b,c,N,t),0,m+1)/mp.factorial(m+1)
    out=(e-cj(N,m+1))/2
    out-=sum(cj(N,m-h)*(-2)**h*mp.stieltjes(h,eta)/mp.factorial(h)
             for h in range(m+1))
    out-=sum(cj(j,q)*2**(m-q)*mp.zeta(1-2*N+2*j,eta,derivative=m-q)
             /mp.factorial(m-q) for j in range(K) if j!=N for q in range(m+1))
    return out


def check_symbolic():
    a,b,c,u=sp.symbols('a b c u')
    shifts=[a/2,b-a/2,c-a/2,1+a/2-b-c-u]
    h=[None]+[-sum(sp.bernoulli(2*k+1,v) for v in shifts)/(k*(2*k+1))
                for k in range(1,3)]
    C=[sp.S.One]
    for j in range(1,3):
        C.append(sp.expand(sum(k*h[k]*C[j-k] for k in range(1,j+1))/j))
        V=2*sp.diff(C[j],a)+sp.diff(C[j],b)+sp.diff(C[j],c)-sp.diff(C[j],u)
        rhs=2*sum(-sp.bernoulli(2*k,a/2)/(2*k)*C[j-k] for k in range(1,j+1))
        assert sp.expand(V-rhs)==0
        rho=(-1)**j*sp.rf(1+a-b-c,j)*sp.rf(1-b,j)*sp.rf(1-c,j)/sp.factorial(j)
        assert sp.expand(C[j].subs(u,-j)-rho)==0
    assert sp.expand(C[1].subs({a:sp.Rational(1,2),b:sp.Rational(1,2),c:sp.Rational(1,2)})
                     -(u**3/3+u**2/4-u/48-sp.Rational(1,16)))==0
    return 'Coefficient differential law and residue polynomial exact through degree j=2; quartic C1 exact.'


def main():
    report={'precision_digits':mp.mp.dps,
            'mpmath_version':mp.__version__,'sympy_version':sp.__version__,
            'method':'Finite sum to n=119 plus centered asymptotic tail through C_11; numerical diagnostics, not rigorous enclosures.',
            'derivative_note':'Hurwitz spectral derivatives use mpmath native derivative= rather than generic differencing; an s=0 second derivative was also checked by Cauchy contour differentiation.',
            'acceptance_absolute_error':'1e-31','symbolic':check_symbolic(),'cases':[]}
    def record(name,actual,expected):
        error=abs(actual-expected)
        report['cases'].append({'name':name,'actual':mp.nstr(actual,45),
                                'expected':mp.nstr(expected,45),'absolute_error':mp.nstr(error,6)})
        print(name,mp.nstr(error,6),flush=True)
        assert error<mp.mpf('1e-31'),(name,error)
    a,b,c=map(mp.mpf,['1.4','.6','.7'])
    d0=1+a-b-c
    for N in range(4):
        rho=(-1)**N*mp.rf(d0,N)*mp.rf(1-b,N)*mp.rf(1-c,N)/mp.factorial(N)
        expected=rho*(mp.digamma(a/2)+(mp.digamma(N+1)-mp.digamma(b)
                   -mp.digamma(c)-mp.digamma(d0+N))/2)
        record('generic integer resonance N='+str(N),completed_series(a,b,c,-N,N+1),expected)
    half=mp.mpf('.5')
    for N,m in [(0,1),(0,2),(1,1),(1,2)]:
        value=mp.diff(lambda t:completed_series(half,half,half,-N+t,N+1),0,m)/mp.factorial(m)
        record('quartic Taylor jet N='+str(N)+', m='+str(m),value,jet_formula(half,half,half,N,m))
    q=mp.mpf('.75')
    record('quarter-parameter half resonance',completed_series(q,q,q,-half,1),
           -mp.mpf(1)/8-mp.sqrt(mp.pi)*(mp.gamma(q)/mp.gamma(mp.mpf('.25')))**3)
    for N in range(3):
        rho=(-1)**N*mp.rf(half,N)**3/mp.factorial(N)
        expected=rho*(mp.harmonic(N)-mp.harmonic(2*N)-mp.pi/2)
        record('quartic moment N='+str(N),completed_series(half,half,half,-N,N+1),expected)
    record('squared-binomial half resonance N=0',completed_series(half,half,half,-half,1),-mp.mpf(1)/4)
    record('squared-binomial half resonance N=1',completed_series(half,half,half,-1-half,2),mp.mpf(21)/128)
    record('squared-binomial harmonic first derivative',
           mp.diff(lambda t:completed_series(half,half,half,-half+t,1),0)/2,
           mp.log(2*mp.pi)/2-mp.loggamma(mp.mpf('.25')))
    record('squared-binomial harmonic second derivative',
           mp.diff(lambda t:completed_series(half,half,half,-half+t,1),0,2)/4,
           -mp.pi/2-mp.zeta(0,mp.mpf('.25'),derivative=2))
    g3=mp.euler+3*mp.log(2)
    explicit=(-g3**2/8+7*g3/48+mp.zeta(2)/16-mp.mpf(1)/16-23*mp.pi/96
              -mp.stieltjes(1,mp.mpf('.25'))/4
              -2*mp.zeta(-1,mp.mpf('.25'),derivative=1))
    record('explicit first-resonance harmonic jet',jet_formula(half,half,half,1,1),explicit)
    record('moving zero first jet',mp.diff(lambda t:r(0,half,half,half,-1+t),0),mp.pi**2/8)
    # A residue zero at b=1 does not license deleting the complete deformation.
    a,b,c=map(mp.mpf,['1.2','1','.6'])
    record('degenerate residue first jet',
           mp.diff(lambda t:completed_series(a,b,c,-1+t,2),0),jet_formula(a,b,c,1,1))
    code_dir=Path(__file__).resolve().parent
    destination=(code_dir.parent/'results'/'dougall_checks.json' if code_dir.name=='code'
                 else code_dir/'gamma_verification.json')
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
