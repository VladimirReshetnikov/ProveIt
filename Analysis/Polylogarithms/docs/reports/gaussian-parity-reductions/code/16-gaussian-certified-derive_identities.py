#!/usr/bin/env python3
"""Exact specializations of the depth-two parity theorem; no numerical fitting.

Convention: D[a,b](x,y) = sum_{n>m>=1} x^n y^m/(n^a m^b).
The general parity input is Panzer (2017), equation (3.2), with its
ascending-index convention reversed. See article.tex for the endpoint limit.
"""
from __future__ import annotations
import json
from pathlib import Path
from math import comb
import sympy as s

PI = s.Symbol('P', real=True)
LOG2 = s.Symbol('L', real=True)

def zeta(k: int):
    if k < 2:
        raise ValueError('The divergent zeta(1) must be cancelled before evaluation.')
    return s.zeta(k).subs(s.pi, PI) if k % 2 == 0 else s.Symbol(f'Z{k}', real=True)

def beta(k: int):
    if k % 2 == 0:
        return s.Symbol(f'B{k}', real=True)
    n = (k-1)//2
    return (-1)**n * s.euler(2*n) * PI**k / (4**(n+1)*s.factorial(2*n))

def li_gaussian(k: int, inverse: bool = False):
    re = -LOG2/2 if k == 1 else -s.Rational(1,2)**k*(1-s.Rational(2)**(1-k))*zeta(k)
    return re + (-s.I if inverse else s.I)*beta(k)

def bernoulli_gaussian(j: int):
    return (2*s.I*PI)**j * s.bernoulli(j,s.Rational(1,4))/s.factorial(j)

def parity_gaussian(a: int,b: int):
    """Return D(i,1)-(-1)^(a+b)D(-i,1), as a depth-one polynomial."""
    if min(a,b)<1:
        raise ValueError('positive indices required')
    w=a+b
    t=sum((-1)**(b+k)*comb(k-1,b-1)*zeta(k)*bernoulli_gaussian(w-k)
          for k in range(b+1,w+1))
    t-=li_gaussian(w)
    t+=(-1)**a*sum(comb(k-1,a-1)*li_gaussian(k,True)*bernoulli_gaussian(w-k)
                   for k in range(a,w+1))
    return s.expand(t)

def reduced_component(a: int,b: int):
    p=parity_gaussian(a,b)
    return s.expand(s.im(p)/2 if (a+b)%2==0 else s.re(p)/2)

def shuffle_row(p: int,q: int):
    w=p+q
    row=[0]*(w-1)
    for j in range(p):row[q+j-1]+=comb(q-1+j,j)
    for j in range(q):row[p+j-1]+=comb(p-1+j,j)
    return row

def lambda_m(m: int):
    if m<2:raise ValueError('m >= 2 required')
    return s.cancel(12*(2**(2*m-1)-1)*s.bernoulli(2*m)/(s.euler(2*m-2)*(2*m)*(2*m-1)))

def odd_family(m: int):
    w=2*m+1
    lam=lambda_m(m)
    aa=shuffle_row(1,w-1);bb=shuffle_row(2,w-2)
    row=[s.Rational(aa[i])-lam*bb[i] for i in range(w-1)]
    c=s.Rational(1,2)**(2*m-1)*(1-s.Rational(2)**(2-2*m))
    rhs=s.expand(-LOG2*beta(2*m)/2+lam*c*beta(2)*zeta(2*m-1))
    return row,rhs

def expected_six():
    P=PI;G=beta(2);Z3=zeta(3);Z5=zeta(5);B4=beta(4);B6=beta(6);L=LOG2
    return {
        (5,1):(-64*P**3*Z3-527*P*Z5+4096*B6)/2048,
        (4,2):(96*P**3*Z3-32*P**2*B4+1581*P*Z5-8448*B6)/1536,
        (3,3):(-3*P**3*Z3+64*P**2*B4-1581*P*Z5+4608*B6)/1024,
        (2,4):(-14*P**4*G+135*P**3*Z3-1440*P**2*B4+23715*P*Z5-69120*B6)/23040,
        (1,5):(-150*P**5*L+56*P**4*G-270*P**3*Z3+1920*P**2*B4-675*P*Z5)/92160,
    }

def latex_expr(e):
    out=s.latex(e)
    out=out.replace('P',r'\pi').replace('L',r'\log 2')
    for k in range(2,50):
        out=out.replace('B_{'+str(k)+'}',r'\beta('+str(k)+')')
        out=out.replace('Z_{'+str(k)+'}',r'\zeta('+str(k)+')')
    return out

def main():
    root=Path(__file__).resolve().parents[1]
    results={}; exact=0
    for w in range(2,13):
        for a in range(1,w):
            b=w-a;p=parity_gaussian(a,b)
            assert s.expand(s.re(p) if w%2==0 else s.im(p))==0
            exact+=1
            e=reduced_component(a,b)
            results[f'{a},{b}']={'component':'imag' if w%2==0 else 'real','expression':str(e),
                                 'latex':latex_expr(e)}
    for ab,e in expected_six().items():
        assert s.expand(reduced_component(*ab)-e)==0;exact+=1
    rr,rhs=odd_family(2)
    assert [s.simplify(960*x) for x in rr]==[960,736,288,576]
    assert s.expand(960*rhs-(21*beta(2)*zeta(3)-480*beta(4)*LOG2))==0
    exact+=2
    odd={}
    for m in range(2,9):
        rr,rhs=odd_family(m)
        A=li_gaussian(1)*li_gaussian(2*m)
        B=li_gaussian(2)*li_gaussian(2*m-1)
        assert s.expand(s.im(A-lambda_m(m)*B)-rhs)==0;exact+=1
        odd[str(2*m+1)]={'lambda':str(lambda_m(m)),'coefficients_a_increasing':list(map(str,rr)),
                         'rhs':str(rhs)}
    (root/'data/identities.json').write_text(json.dumps({'parity':results,'odd_shuffle_family':odd},indent=2)+'\n')
    # Each row is an individual display; no over-wide multirow table.
    for w in (8,10):
        blocks=[]
        for a in reversed(range(1,w)):
            e=reduced_component(a,w-a)
            den=s.ilcm(*[s.denom(t) for t in s.Add.make_args(e)])
            lhs=(str(den) if den!=1 else '')+rf' g_{{{a},{w-a}}}'
            terms=s.Add.make_args(s.expand(den*e))
            # Three terms per line, preserving the sign at each continuation.
            groups=[latex_expr(s.Add(*terms[j:j+3])) for j in range(0,len(terms),3)]
            rhsx=groups[0]
            for group in groups[1:]:
                sign='' if group.lstrip().startswith('-') else '+'
                rhsx+=r'\\ &\quad {}'+sign+group
            blocks.append(r'\begin{equation}\begin{split}'+lhs+' &= '+rhsx+r'\end{split}\end{equation}')
        (root/f'generated/weight{w}.tex').write_text('\n'.join(blocks)+'\n')
    (root/'data/symbolic_summary.json').write_text(json.dumps({'exact_checks':exact,'parity_rows':len(results),
        'existing_weight_six_rows_proved':5,'existing_weight_five_relation_proved':1,
        'odd_family_instances':len(odd)},indent=2)+'\n')
    print(json.dumps({'exact_checks':exact,'parity_rows':len(results),'lambda_m3':str(lambda_m(3))}))

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Verification requires assertions: do not run Python with -O.')
    main()
