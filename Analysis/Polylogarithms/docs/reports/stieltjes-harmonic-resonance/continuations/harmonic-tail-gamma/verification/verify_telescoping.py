#!/usr/bin/env python3
"""Independent exact finite telescoping certificates for even harmonic tails."""
import json
from pathlib import Path
import sympy as s

N, x, A, B = s.symbols('N x A B')
T=s.symbols('T')

def symmetric_polynomial(poly):
    remaining=s.expand(poly)
    result=s.S.Zero
    while remaining != 0:
        pol=s.Poly(remaining,N)
        assert pol.degree()%2==0
        degree=pol.degree()//2
        coefficient=pol.LC()
        result+=coefficient*T**degree
        remaining=s.expand(remaining-coefficient*(N*(N+1))**degree)
    return s.factor(result)

def power_sum(k, upper):
    return s.expand((s.bernoulli(k+1, upper+1)-s.bernoulli(k+1))/(k+1))

def polynomial_sum(poly):
    return s.expand(sum(c*power_sum(k[0], N) for k,c in s.Poly(poly,N).terms()))

def laurent_terms(expr, var):
    out={}
    for term in s.Add.make_args(s.expand(expr)):
        power=int(term.as_powers_dict().get(var,0))
        out[power]=out.get(power,0)+s.cancel(term/var**power)
    return {k:s.cancel(v) for k,v in out.items() if v != 0}

def source_entry(p,q,j,k):
    d=2*j+1
    e=d-p-q+2*k+1
    if e<0:
        return s.S.Zero
    val=s.S.Zero
    for top,low in ((d-q+1,p-2*k),(d-p+1,q-2*k)):
        if 2<=low<=top:
            val+=s.binomial(top,low)/top
    return s.bernoulli(e)*val

def centered_tail(r,terms):
    return x**(1-r)/s.Integer(r-1)+sum(
        s.bernoulli(2*k,s.Rational(1,2))*s.rf(r,2*k-1)/s.factorial(2*k)
        *x**(1-r-2*k) for k in range(1,terms+1))

def build(p,q,weights):
    assert p%2==q%2==0 and 2<=p<=q
    assert all(j>=q//2 for j in weights)
    K=s.expand(sum(v*N**(2*j+1) for j,v in weights.items()))
    P=s.expand(K.subs(N,x+s.Rational(1,2))-K.subs(N,x-s.Rational(1,2)))
    U=polynomial_sum(s.cancel(K/N**q))
    V=polynomial_sum(s.cancel(K/N**p))
    H=s.expand(K/N**(p+q)+U.subs(N,N-1)/N**p+V.subs(N,N-1)/N**q)
    ht=laurent_terms(H,N)
    assert all(k%2==0 for k in ht)
    for k in range(q//2):
        assert s.expand(ht.get(-2*k,0)-sum(v*source_entry(p,q,j,k) for j,v in weights.items()))==0
    hpoly=sum(c*N**k for k,c in ht.items() if k>=0)
    hneg=sum(c*N**k for k,c in ht.items() if k<0)
    delta=2*max(weights)+2-p-q
    terms=max(0,delta//2)+2
    pt=laurent_terms(s.expand(P*centered_tail(p,terms)*centered_tail(q,terms)),x)
    S=s.expand(sum(v*x**k for k,v in pt.items() if k>=0))
    R=polynomial_sum(s.expand(hpoly-S.subs(x,N-s.Rational(1,2))))
    F=K*A*B+U*A+V*B+R
    prev=F.subs({N:N-1,A:A+N**(-p),B:B+N**(-q)}, simultaneous=True)
    target=P.subs(x,N-s.Rational(1,2))*(A+N**(-p))*(B+N**(-q))-S.subs(x,N-s.Rational(1,2))-hneg
    assert s.cancel(F-prev-target)==0
    assert all(expr.subs(N,0)==0 for expr in (K,U,V,R))
    # Entirely independent finite Laurent calculation of the limiting constant.
    def tail_at_N(r):
        return N**(1-r)/s.Integer(r-1)-N**(-r)/2+sum(
            s.bernoulli(2*k)*s.rf(r,2*k-1)/s.factorial(2*k)*N**(1-r-2*k)
            for k in range(1,max(0,delta//2)+4))
    fterms=laurent_terms(F.subs({A:tail_at_N(p),B:tail_at_N(q)}),N)
    assert all(v==0 for k,v in fterms.items() if k>0)
    assert s.cancel(fterms.get(0,s.S.Zero)+ht.get(0,s.S.Zero)/2)==0
    return {
        'p':p,'q':q,'weights':{str(j):str(v) for j,v in weights.items()},
        'K':str(s.factor(K)), 'P':str(P), 'U':str(s.factor(U)),
        'V':str(s.factor(V)), 'H':str(s.factor(H)), 'S':str(S), 'R':str(s.factor(R)),
        'h_coordinates':{str(k):str(ht.get(-2*k,0)) for k in range(q//2)},
        'limit':str(-ht.get(0,s.S.Zero)/2),
        'K_latex':s.latex(s.factor(K)), 'P_latex':s.latex(P),
        'U_latex':s.latex(s.factor(U)), 'V_latex':s.latex(s.factor(V)),
        'H_latex':s.latex(s.factor(H)), 'S_latex':s.latex(S), 'R_latex':s.latex(s.factor(R)),
        'U_symmetric':str(symmetric_polynomial(U)),
        'V_symmetric':str(symmetric_polynomial(V)),
        'U_symmetric_latex':s.latex(symmetric_polynomial(U)),
        'V_symmetric_latex':s.latex(symmetric_polynomial(V)),
        'finite_identity_verified':True,'constant_term_verified':True,
        'source_coordinates_verified':True
    }

def main():
    cases=[(p,q,{q//2:s.S.One}) for p,q in ((2,2),(2,4),(4,6),(4,8),(6,10),(8,12),(8,16))]
    cases += [(4,6,{3:-28,4:180,5:264}),
              (8,12,dict(zip(range(6,12),map(s.Integer,(469839,1269227,-11819495,56443363,83672540,12834702)))))]
    result=[build(*case) for case in cases]
    dest=Path(__file__).resolve().parent.parent/'data'/'telescoping_results.json'
    dest.write_text(json.dumps(result,indent=2))
    print(json.dumps({'cases':len(result),'all_exact_checks_passed':True,'file':str(dest),'812':result[-1]},indent=2))

if __name__=='__main__':
    main()
