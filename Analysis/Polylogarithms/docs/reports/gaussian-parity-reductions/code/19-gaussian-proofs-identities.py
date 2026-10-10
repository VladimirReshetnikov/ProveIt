"""Exact polynomial generation from the two proved functional identities.

SymPy is used only for rational polynomial arithmetic.  No recognition,
integer-relation algorithm, or numerical equality test is used here.
"""

from functools import lru_cache
import sympy as s

pi, ell = s.symbols("pi ell", real=True)
G = s.Symbol("G", real=True)


def zeta(n):
    if n < 2:
        raise ValueError("The divergent value zeta(1) is never an atom")
    if n % 2:
        return s.Symbol(f"zeta_{n}", real=True)
    m = n // 2
    return (-1)**(m + 1) * s.bernoulli(n) * (2*pi)**n / (2*s.factorial(n))


def beta(n):
    if n == 2:
        return G
    if n % 2 == 0:
        return s.Symbol(f"beta_{n}", real=True)
    m = (n - 1) // 2
    return (-1)**m * s.euler(2*m) * pi**n / (4**(m + 1)*s.factorial(2*m))


def single_gaussian(n, conjugate=False):
    real = -ell/2 if n == 1 else -s.Rational(1, 2**n)*(1-s.Rational(1, 2**(n-1)))*zeta(n)
    return real + (-s.I if conjugate else s.I)*beta(n)


def bernoulli_gaussian(n):
    return (2*s.I*pi)**n*s.bernoulli(n, s.Rational(1, 4))/s.factorial(n)


@lru_cache(None)
def double_parity(a, b):
    """F_ab(i)-(-1)**(a+b) F_ab(-i), via the specialized Panzer formula."""
    w = a + b
    result = -single_gaussian(w)
    result += sum((-1)**k*s.binomial(b+k-1, b-1)*zeta(b+k)*
                  bernoulli_gaussian(a-k) for k in range(1, a+1))
    result += (-1)**a*sum(s.binomial(a+k-1, a-1)*
                         single_gaussian(a+k, conjugate=True)*
                         bernoulli_gaussian(b-k) for k in range(b+1))
    return s.expand(result)


def double_polynomial(a, b):
    """Even weight -> imaginary part; odd weight -> real part."""
    result = double_parity(a, b)
    if (a+b) % 2 == 0:
        assert s.expand(s.re(result)) == 0
        return s.expand(s.im(result)/2)
    assert s.expand(s.im(result)) == 0
    return s.expand(s.re(result)/2)


def half_gaussian(n):
    L = -ell/2 + s.I*pi/4
    if n == 1:
        return -s.conjugate(L)
    if n == 2:
        return 5*pi**2/96-ell**2/8+s.I*(G-pi*ell/8)
    if n == 3:
        return (35*zeta(3)/64-5*pi**2*ell/192+ell**3/48+
                s.I*s.Symbol("lambda_3", real=True))
    return s.Symbol(f"mu_{n}", real=True)+s.I*s.Symbol(f"lambda_{n}", real=True)


@lru_cache(None)
def one_two_polynomial(a, b):
    """Full complex value Li_{1^a,2,1^b}(i,1,...,1)."""
    w, L = a+b+2, -ell/2+s.I*pi/4
    result = sum((-1)**(a+k)*s.binomial(k-1,a)*L**(w-k)/s.factorial(w-k)*
                 half_gaussian(k) for k in range(a+1,w+1))
    result += (-1)**(b+1)*sum(s.binomial(b+j+1,j)*L**(a-j)/s.factorial(a-j)*
                            zeta(b+j+2) for j in range(a+1))
    return s.expand(result-L**w/s.factorial(w))


def manuscript_double_rows():
    z3,z5,B4,B6=zeta(3),zeta(5),beta(4),beta(6)
    return {
        (5,1):(-64*pi**3*z3-527*pi*z5+4096*B6)/2048,
        (4,2):(96*pi**3*z3-32*pi**2*B4+1581*pi*z5-8448*B6)/1536,
        (3,3):(-3*pi**3*z3+64*pi**2*B4-1581*pi*z5+4608*B6)/1024,
        (2,4):(-14*pi**4*G+135*pi**3*z3-1440*pi**2*B4+
               23715*pi*z5-69120*B6)/23040,
        (1,5):(-150*pi**5*ell+56*pi**4*G-270*pi**3*z3+
               1920*pi**2*B4-675*pi*z5)/92160,
    }


def manuscript_triple_rows():
    la3,la4=s.symbols("lambda_3 lambda_4",real=True)
    z3=zeta(3)
    return {
        (0,2):la4+la3*ell/2-G*(pi**2-4*ell**2)/32-pi*(8*ell**3+105*z3)/768,
        (1,1):-3*la4-la3*ell+G*(pi**2-4*ell**2)/32-3*pi**3*ell/256+
              pi*(2*ell**3+67*z3)/128,
        (2,0):3*la4+la3*ell/2+5*pi**3*ell/192-163*pi*z3/256,
    }


def polynomial_terms(expression):
    """Portable rational coefficient/exponent representation."""
    expression=s.expand(expression)
    symbols=sorted(expression.free_symbols,key=str)
    if not symbols:
        return [{"coefficient":str(expression),"powers":{}}]
    return [{"coefficient":str(coefficient),
             "powers":{str(v):int(e) for v,e in zip(symbols,exponents) if e}}
            for exponents,coefficient in s.Poly(expression,*symbols).terms()]


def exact_checks():
    checks=[]
    for (a,b),target in manuscript_double_rows().items():
        assert s.expand(double_polynomial(a,b)-target)==0
        checks.append({"name":f"manuscript_g{a}{b}","residual":"0"})
    for (a,b),target in manuscript_triple_rows().items():
        assert s.expand(s.im(one_two_polynomial(a,b))-target)==0
        checks.append({"name":f"manuscript_one2_{a}_{b}","residual":"0"})
    return checks


if __name__=="__main__":
    import json
    print(json.dumps(exact_checks(),indent=2))
