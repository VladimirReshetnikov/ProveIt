"""Generate weight-eight Gaussian depth-two imaginary parts exactly.

Every relation used is either a double-zeta stuffle, a double-zeta shuffle,
the depth-two sum theorem, or the proved inversion formula in the note.
"""

import sympy as s
from functools import lru_cache

I,pi=s.I,s.pi
L=s.symbols('L')
G,B4,B6,B8=s.symbols('G beta4 beta6 beta8',real=True)
Z3,Z5,Z7,Z9=s.symbols('zeta3 zeta5 zeta7 zeta9',real=True)
lg=s.symbols('log2',real=True)

def zeta(n):
    return {3:Z3,5:Z5,7:Z7,9:Z9}.get(n,s.zeta(n))

@lru_cache(None)
def odd_double_table(w):
    assert w>=3 and w%2
    unknowns={a:s.Symbol(f'Z{a}_{w-a}') for a in range(2,w)}
    rows=[sum(unknowns.values())-zeta(w)]
    for p in range(2,w-1):
        q=w-p
        rows.append(unknowns[p]+unknowns[q]+zeta(w)-zeta(p)*zeta(q))
        shuffle=sum(s.binomial(q-1+k,k)*unknowns[q+k] for k in range(p))
        shuffle+=sum(s.binomial(p-1+k,k)*unknowns[p+k] for k in range(q))
        rows.append(shuffle-zeta(p)*zeta(q))
    mat,rhs=s.linear_eq_to_matrix(rows,list(unknowns.values()))
    sol=s.linsolve((mat,rhs),list(unknowns.values()))
    assert len(sol)==1
    values=next(iter(sol))
    assert not any(v.has(*unknowns.values()) for v in values)
    assert all(s.expand(row.subs(dict(zip(unknowns.values(),values))))==0 for row in rows)
    return {a:s.expand(v) for a,v in zip(unknowns,values)}

def Q(n,x):
    return s.expand(-(2*pi*I)**n/s.factorial(n)*s.bernoulli(n,x/(2*pi*I)))

def li(n):
    if n==1:return -lg/2+I*pi/4
    be={2:G,3:pi**3/32,4:B4,5:5*pi**5/1536,6:B6,
        7:61*pi**7/184320,8:B8}[n]
    return -s.Rational(1,2**n)*(1-s.Rational(1,2**(n-1)))*zeta(n)+I*be

def R1(a,b):
    return s.expand(Q(a+b,0)-zeta(a+b)+sum(
        (-1)**k*s.binomial(a+k-1,k)*Q(b-k,0)*zeta(a+k)
        for k in range(b+1)))

def c(a,b):
    if a==1:return (-1)**(b+1)*b*zeta(b+1)
    p=2*odd_double_table(a+b)[a] if (a+b)%2 else 0
    return s.expand(p-R1(a,b))

def g(a,b):
    x=I*pi/2
    R=Q(a+b,x)-li(a+b)+sum(
        (-1)**k*s.binomial(a+k-1,k)*Q(b-k,x)*li(a+k)
        for k in range(b+1))
    P=s.expand(R+sum(c(a-j,b)*x**j/s.factorial(j) for j in range(a)))
    assert s.simplify(s.re(P))==0
    return s.expand(P/(2*I))

if __name__=='__main__':
    for w in (3,5,7):
        print('Odd double-zeta table, weight',w,':',odd_double_table(w))
    for b in range(1,8):
        v=g(8-b,b)
        denominators=[s.denom(v.coeff(term)) for term in
              [B8,pi**2*B6,pi**4*B4,pi**6*G,pi**7*lg,pi**5*Z3,pi**3*Z5,pi*Z7]]
        d=s.ilcm(*denominators)
        print('\n',d,'g_'+str(8-b)+str(b),'=',s.expand(d*v))
        print('LaTeX:',s.latex(s.expand(d*v)))
