"""Exact finite algebra for the digamma-power bridge."""
from functools import lru_cache
from collections import Counter
import sympy as sp

g = sp.Symbol('g')
class ZetaSymbols(dict):
    def __missing__(self, k):
        self[k] = g if k == 1 else sp.Symbol(f'z{k}')
        return self[k]

zz = ZetaSymbols()

@lru_cache(None)
def harmonic_symbols(k):
    return sp.symbols(f'h1:{k+1}')
v, eps = sp.symbols('v eps')

@lru_cache(None)
def stuffle(a, b):
    if not a:
        return {b: 1}
    if not b:
        return {a: 1}
    result = Counter()
    for w, c in stuffle(a[1:], b).items():
        result[(a[0],)+w] += c
    for w, c in stuffle(a, b[1:]).items():
        result[(b[0],)+w] += c
    for w, c in stuffle(a[1:], b[1:]).items():
        result[(a[0]+b[0],)+w] += c
    return dict(result)

def multiply_words(left, right):
    out = Counter()
    for a, ca in left.items():
        for b, cb in right.items():
            for w, c in stuffle(a,b).items():
                out[w] += ca*cb*c
    return dict(out)

@lru_cache(None)
def harmonic_monomial(powers):
    result = {():1}
    for r, exponent in enumerate(powers,1):
        for _ in range(exponent):
            result = multiply_words(result,{(r,):1})
    return result

def word_coefficients(polynomial, k):
    """Input polynomial in v=1/n and H_{n-1}^{(r)}, with positive v powers."""
    if sp.expand(polynomial)==0:
        return {}
    out = {}
    for exponents, coefficient in sp.Poly(sp.expand(polynomial),v,*harmonic_symbols(k)).terms():
        q, powers = exponents[0], exponents[1:]
        assert q >= 1, (polynomial,exponents)
        for tail, mult in harmonic_monomial(powers).items():
            word = (q,)+tail
            out[word] = out.get(word,0)+coefficient*mult
    return {w:sp.expand(c) for w,c in out.items() if sp.expand(c)!=0}

@lru_cache(None)
def regularized(word):
    if not word:
        return sp.Integer(1)
    if word==(1,):
        return g
    if word[0]>=2:
        if len(word)==1:
            return zz[word[0]]
        return sp.Symbol('Z_'+'_'.join(map(str,word)))
    rows = dict(stuffle((1,),word[1:]))
    mult = rows.pop(word)
    return sp.expand((g*regularized(word[1:])-
                     sum(c*regularized(w) for w,c in rows.items()))/mult)

def reduce_small(expr):
    expr = sp.sympify(expr)
    z2,z3,z4,z5 = (zz[k] for k in range(2,6))
    rules = {
        (2,1):z3,
        (3,1):z4/4,
        (2,2):3*z4/4,
        (2,1,1):z4,
        (4,1):2*z5-z2*z3,
        (3,2):3*z2*z3-sp.Rational(11,2)*z5,
        (2,3):-2*z2*z3+sp.Rational(9,2)*z5,
        (3,1,1):2*z5-z2*z3,
        (2,2,1):3*z2*z3-sp.Rational(11,2)*z5,
        (2,1,2):-2*z2*z3+sp.Rational(9,2)*z5,
        (2,1,1,1):z5,
    }
    expr = expr.subs({sp.Symbol('Z_'+'_'.join(map(str,w))):val
                      for w,val in rules.items()})
    expr = sp.expand(expr).subs(z2**2,sp.Rational(5,2)*z4)
    return sp.expand(expr)

def power_data(k):
    if not isinstance(k, int) or k < 1:
        raise ValueError("The power must be a positive integer.")
    hh = harmonic_symbols(k)
    # Truncation keeps polynomial cost modest even at order eight.
    f = -1+(hh[0]-g)*eps+sum((hh[r-1]+(-1)**r*zz[r])*eps**r
                              for r in range(2,k+1))
    coeffs=[sp.Integer(1)]+[sp.Integer(0)]*k
    fcoeff=[-1,hh[0]-g]+[hh[r-1]+(-1)**r*zz[r] for r in range(2,k+1)]
    for _ in range(k):
        coeffs=[sp.expand(sum(coeffs[a]*fcoeff[b] for a in range(i+1)
                             for b in [i-a])) for i in range(k+1)]
    p={j:coeffs[k-j] for j in range(1,k+1)}
    kappa=sp.expand(coeffs[k].subs({h:0 for h in hh}))
    shift={hh[r-1]:hh[r-1]+v**r for r in range(1,k+1)}
    pn={j:sp.expand(pj.subs(shift,simultaneous=True)) for j,pj in p.items()}
    delta={j:sp.expand(pn[j]-p[j]) for j in p}
    elementary_polynomial=-v*pn[1]
    for j in range(2,k+1):
        elementary_polynomial += delta[j]*v**(j-1)/sp.Integer(j-1)-pn[j]*v**j
    elementary_words=word_coefficients(elementary_polynomial,k)
    elementary=sp.expand(kappa+sum(c*regularized(w) for w,c in elementary_words.items()))
    derivative_words=word_coefficients(delta[1],k)
    jpoly=sp.expand(sum(delta[j]*v**(j-1)/sp.Integer(j-1) for j in range(2,k+1)))
    jwords=word_coefficients(jpoly,k) if jpoly else {}
    return dict(jpolynomial=jpoly,jwords=jwords,k=k,p=p,pn=pn,delta=delta,kappa=kappa,
                elementary_words=elementary_words,
                elementary=elementary,elementary_small=reduce_small(elementary),
                derivative_words=derivative_words)

if __name__=='__main__':
    for k in range(2,6):
        data=power_data(k)
        print('POWER',k)
        print('ELEMENTARY',data['elementary_small'])
        print('DERIVATIVES',data['derivative_words'])
