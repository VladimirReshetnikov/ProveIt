"""Exact Gaussian depth-two parity formulas, using only rational arithmetic.

This implements the finite Bernoulli specialization of Panzer (2017),
equation (3.2), after reversing his ascending-index convention.
Run as `python gaussian_parity.py` for the complete weight 6 and 8 tables.
The functions accept arbitrary positive indices of even total weight.
"""
import argparse
import json
from pathlib import Path
import sympy as s

pi,I=s.pi,s.I
log2=s.Symbol('log2',real=True)

def zeta(n):
    return s.Symbol(f'zeta{n}',real=True) if n%2 else s.zeta(n)

def beta(n):
    if not n%2:
        return s.Symbol('G' if n==2 else f'beta{n}',real=True)
    k=(n-1)//2
    return (-1)**k*s.euler(2*k)*pi**n/(4**(k+1)*s.factorial(2*k))

def single_minus_i(n):
    if n==1:return -log2/2-I*pi/4
    return -s.Rational(1,2**n)*(1-s.Rational(1,2**(n-1)))*zeta(n)-I*beta(n)

def bernoulli_i(n):
    return (2*pi*I)**n/s.factorial(n)*s.bernoulli(n,s.Rational(1,4))

def from_complex_formula(a,b):
    assert a>=1 and b>=1 and (a+b)%2==0
    w=a+b
    p=-s.conjugate(single_minus_i(w))
    p+=sum((-1)**k*s.binomial(b+k-1,b-1)*zeta(b+k)*bernoulli_i(a-k)
           for k in range(1,a+1))
    p+=(-1)**a*sum(s.binomial(a+k-1,a-1)*single_minus_i(a+k)*bernoulli_i(b-k)
                         for k in range(b+1))
    p=s.expand(p)
    assert s.simplify(s.re(p))==0
    return s.expand(p/(2*I))

def binom_index(mu,idx):
    return s.binomial(mu-1,idx-1) if mu>=idx else s.S.Zero

def rational_bernoulli(n):
    return 2**n*s.bernoulli(n,s.Rational(1,4))/s.factorial(n)

def from_real_coefficients(a,b):
    assert a>=1 and b>=1 and (a+b)%2==0
    w=a+b
    out=s.S.Zero
    for mu in range(2,w+1,2):
        coeff=((-1)**(a+1+(w-mu)//2)*binom_index(mu,a)*rational_bernoulli(w-mu)
               -(1 if mu==w else 0))/2
        out+=coeff*pi**(w-mu)*beta(mu)
    for mu in range(3,w,2):
        c_mu=s.Rational(1,2**mu)*(1-s.Rational(1,2**(mu-1)))
        coeff=s.Rational(1,2)*(-1)**(a+1+(w-mu-1)//2)*rational_bernoulli(w-mu)
        coeff*=binom_index(mu,b)-(1 if mu==b else 0)+c_mu*binom_index(mu,a)
        out+=coeff*pi**(w-mu)*zeta(mu)
    if a==1:
        out+=(-1)**(w//2-1)*rational_bernoulli(w-1)*pi**(w-1)*log2/4
    return s.expand(out)

def coefficient_record(a,b):
    w=a+b
    expr=from_real_coefficients(a,b)
    bases=[pi**(w-mu)*beta(mu) for mu in range(2,w+1,2)]
    bases+=[pi**(w-mu)*zeta(mu) for mu in range(3,w,2)]
    bases+=[pi**(w-1)*log2]
    coeffs=[s.expand(expr).coeff(x) for x in bases]
    assert s.expand(sum(c*x for c,x in zip(coeffs,bases))-expr)==0
    scale=s.ilcm(*[s.denom(c) for c in coeffs])
    return {'a':a,'b':b,'scale':int(scale),'basis':[str(x) for x in bases],
            'scaled_coefficients':[int(scale*c) for c in coeffs]}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=
        Path(__file__).resolve().parents[3]/'results'/'independent'/'parity'/'gaussian_coefficients.json')
    args=parser.parse_args()
    import extend_weight8 as ex
    records=[]
    for w in (6,8):
        for b in range(1,w):
            a=w-b
            direct=from_complex_formula(a,b)
            rational=from_real_coefficients(a,b)
            ode=ex.g(a,b)
            assert s.expand(direct-rational)==0
            assert s.expand(direct-ode)==0
            rec=coefficient_record(a,b)
            print(rec)
            records.append(rec)
    # A broad symbolic consistency check is cheap and does not claim a new
    # theorem at each weight: the mathematics already proves the formula.
    for w in range(2,22,2):
        for b in range(1,w):
            assert s.expand(from_complex_formula(w-b,b)-from_real_coefficients(w-b,b))==0
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('w') as out:
        json.dump({'formula':'finite Bernoulli specialization of depth-two inversion',
                   'exact_identity_checks':12,'complex_real_consistency_checks':100,
                   'records':records},out,indent=2)
    print('All 12 ODE/direct identities and 100 complex/real formula comparisons are exact.')
