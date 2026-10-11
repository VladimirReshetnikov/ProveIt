"""Exact finite certificates and independent normal-jet diagnostics.

The exact checks certify the displayed finite rational identities.
The convergent Mellin quadratures are numerical diagnostics, not
interval-arithmetic bounds and not substitutes for the analytic proofs.
"""
import json
from pathlib import Path

import mpmath as mp
import sympy as sy
from sympy.functions.combinatorial.numbers import stirling

mp.mp.dps=60
t,u,n=sy.symbols('t u n')


def negative_polylog(a,z):
    w=sy.symbols('w')
    f=w/(1-w)
    for _ in range(a):
        f=sy.cancel(w*sy.diff(f,w))
    return sy.cancel(f.subs(w,z))


def reduce_rational(data):
    f=sy.cancel(sy.prod(negative_polylog(a,x*t**p) for a,p,x in data))
    num,den=sy.fraction(f)
    roots=sy.roots(den,t)
    assert sum(roots.values())==sy.degree(den,t)
    cinf=sy.limit(f,t,sy.oo)
    reconstructed=cinf
    out={}
    for pole,multiplicity in roots.items():
        alpha=1/pole
        hol=sy.cancel((1-alpha*t)**multiplicity*f)
        for h in range(1,multiplicity+1):
            c=sy.simplify(sy.diff(hol,t,multiplicity-h).subs(t,pole)
                          *(-1/alpha)**(multiplicity-h)
                          /sy.factorial(multiplicity-h))
            reconstructed+=c/(1-alpha*t)**h
            e=sy.Poly(sy.prod(1+u/j for j in range(1,h)),u)
            for r in range(h):
                key=(alpha,r)
                out[key]=sy.simplify(out.get(key,0)+c*e.nth(r))
    assert sy.cancel(sy.together(f-reconstructed))==0
    return f,out


def coefficients_direct(data,N):
    arr=[sy.S.One]+[sy.S.Zero]*N
    for a,p,x in data:
        b=[sy.S.Zero]*(N+1)
        for j in range(1,N//p+1):
            b[p*j]=sy.Integer(j)**a*x**j
        arr=[sum(arr[j]*b[k-j] for j in range(k+1)) for k in range(N+1)]
    return arr


def exact_checks():
    x,y=sy.symbols('x y',nonzero=True)
    counts={}
    for a in range(1,6):
        for b in range(1,6):
            rhs=sum(sy.binomial(a+b-j-1,b-1)/(x**j*(x+y)**(a+b-j))
                    for j in range(1,a+1))
            rhs+=sum(sy.binomial(a+b-j-1,a-1)/(y**j*(x+y)**(a+b-j))
                     for j in range(1,b+1))
            assert sy.cancel(rhs-1/(x**a*y**b))==0
    counts['positive_partial_fractions']=25
    for d in range(1,13):
        lhs=sy.prod(n-j for j in range(1,d))
        rhs=sum(stirling(d,r+1,kind=1,signed=True)*n**r for r in range(d))
        assert sy.expand(lhs-rhs)==0
    counts['confluent_composition_polynomials']=12
    for h in range(1,15):
        p=sy.Poly(sy.prod(1+u/j for j in range(1,h)),u)
        for r in range(h):
            assert p.nth(r)==stirling(h,r+1,kind=1)/sy.factorial(h-1)
    counts['harmonic_stirling_coefficients']=105
    models=[[(0,1,sy.Rational(1,2)),(0,1,sy.Rational(1,3))],
            [(0,1,-1)],[(0,1,-1)]*3,
            [(1,1,-1),(2,1,-1)],
            [(0,2,1),(0,1,-1)],
            [(2,1,-1),(0,1,1)],
            [(0,2,-1),(1,1,-1)]]
    for data in models:
        f,reduced=reduce_rational(data)
        direct=coefficients_direct(data,36)
        for k in range(1,37):
            predicted=sum(v*alpha**k*k**r for (alpha,r),v in reduced.items())
            assert sy.simplify(predicted-direct[k])==0
    counts['rational_generators_reconstructed']=len(models)
    counts['weighted_confluent_coefficients']=len(models)*36
    certificate=t**5-t**7-t**8+t**9+t**10-t**12
    assert sy.expand(certificate*(1+t**2)*(1+t**3)-t**5*(1-t**12))==0
    counts['cyclotomic_polynomial_certificates']=1
    return counts


def mellin_first(f,f0,difference):
    return mp.quad(lambda t:difference(t)/t,[0,1]) \
         +mp.quad(lambda t:f(t)/t,[1,2,4,8,mp.inf])+mp.euler*f0


def numeric_checks():
    records=[]
    def record(label,value,expected):
        error=abs(value-expected)
        assert error<mp.mpf('1e-52')
        records.append({'name':label,'mellin':mp.nstr(value,53),
                        'closed_form':mp.nstr(expected,53),
                        'absolute_error':mp.nstr(error,8)})
    value=mellin_first(lambda t:1/(mp.exp(2*t)+1),mp.mpf(1)/2,
                       lambda t:-mp.tanh(t)/2)
    record('distinct_colors_i_minus_i',value,mp.log(mp.pi/4)/2)

    def pairdiff(t):
        q=mp.exp(-t)
        return mp.expm1(-t)*(3*q+1)/(4*(1+q)**2)
    value=mellin_first(lambda t:1/(mp.exp(t)+1)**2,mp.mpf(1)/4,pairdiff)
    record('double_color_minus_one',value,3*mp.zeta(-1,derivative=1)
           -mp.log(2)/6+mp.log(mp.pi)/2)

    def triplediff(t):
        q=mp.exp(-t)
        return -mp.expm1(-t)*(7*q*q+4*q+1)/(8*(1+q)**3)
    value=mellin_first(lambda t:-1/(mp.exp(t)+1)**3,-mp.mpf(1)/8,triplediff)
    record('triple_color_minus_one',value,-7*mp.zeta(3)/(8*mp.pi**2)
           -mp.mpf(9)/2*mp.zeta(-1,derivative=1)-mp.log(mp.pi)/2)

    def weightdiff(t):
        q=mp.exp(-t)
        return mp.expm1(-t)*(3*q**4+3*q**3+2*q*q+q+1) \
             /(4*(1+q*q)*(1+q**3))
    value=mellin_first(lambda t:1/((mp.exp(2*t)+1)*(mp.exp(3*t)+1)),
                      mp.mpf(1)/4,weightdiff)
    expected=mp.loggamma(mp.mpf(5)/12)+mp.loggamma(mp.mpf(3)/4) \
            +mp.loggamma(mp.mpf(5)/6)-mp.loggamma(mp.mpf(7)/12) \
            -mp.loggamma(mp.mpf(2)/3)-mp.log(12)/4
    record('weights_2_3_gamma_quotient',value,expected)

    for q in (3,4,5,6,12):
        alpha=mp.exp(2j*mp.pi/q)
        f0=alpha/(1-alpha)
        value=mellin_first(lambda t:alpha*mp.exp(-t)/(1-alpha*mp.exp(-t)),
                          f0,lambda t:alpha*mp.expm1(-t)
                          /((1-alpha*mp.exp(-t))*(1-alpha)))
        expected=mp.fsum(alpha**j*mp.loggamma(mp.mpf(j)/q) for j in range(1,q+1))
        expected-=mp.log(q)*f0
        record('root_gamma_q_'+str(q),value,expected)
    return records


def main():
    counts=exact_checks()
    print(json.dumps(counts),flush=True)
    records=numeric_checks()
    print(json.dumps(records,indent=2),flush=True)
    report={'exact_certificate_counts':counts,'numeric_precision':mp.mp.dps,
            'qualification':'numeric quadratures are not interval certified',
            'numeric_records':records}
    (Path(__file__).resolve().parents[1]/'results'/'spectral_results.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
