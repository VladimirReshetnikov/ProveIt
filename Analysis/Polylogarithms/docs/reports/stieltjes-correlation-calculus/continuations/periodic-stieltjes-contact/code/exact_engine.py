#!/usr/bin/env python3
"""Exact rational/symbolic replay for periodic Stieltjes contact identities.

No numerical integer-relation search is used.  The finite checks test formula
implementations; the all-index theorem is proved in article.tex.
"""
from __future__ import annotations
import json, platform
from functools import lru_cache
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
u,v,L=s.symbols('u v L')


def cut(expr, degree):
    return s.Add(*[c*u**i*v**j for (i,j),c in s.Poly(s.expand(expr),u,v).terms()
                  if i+j<=degree])


def exp_cut(expr, degree):
    ans=s.Integer(1); term=s.Integer(1)
    for j in range(1,degree+1):
        term=cut(term*expr/j,degree)
        if term==0:break
        ans+=term
    return s.expand(ans)


@lru_cache(None)
def P(p,x):
    if p<0:raise ValueError('Nonnegative derivative order required.')
    return s.expand(s.prod(1+x/s.Integer(j) for j in range(1,p+1)))


def A_series(degree):
    logA=sum(s.zeta(k)/k*(u**k+v**k-(u+v)**k) for k in range(2,degree+1))
    logA-=sum((1-s.Rational(1,2)**(2*j))*s.zeta(2*j)/j
              *((u-v)**(2*j)-(u+v)**(2*j)) for j in range(1,degree//2+1))
    return exp_cut(logA,degree)


def E_series(degree):
    return exp_cut(sum(s.zeta(k)/k*(u**k+(-1)**k*(u+v)**k-(-1)**k*v**k)
                       for k in range(2,degree+1)),degree)


def gamma_series(phase,degree):
    # L means gamma + log(2*pi*|k|).
    x=s.symbols('x')
    logg=(L+phase)*x+sum(s.zeta(k)*x**k/k for k in range(2,degree+1))
    out=1;term=1
    for j in range(1,degree+1):
        term=s.Poly(s.expand(term*logg/j),x)
        term=s.Add(*[c*x**a[0] for a,c in term.terms() if a[0]<=degree])
        out+=term
    return s.Poly(s.expand(out),x)


def main():
    max_degree=7 # m+n <= 5 requires contact numerator through degree 7
    A=A_series(max_degree)
    checks=[];formulas=[]
    def check(group,params,expr):
        if s.expand(expr)!=0:raise AssertionError((group,params,s.expand(expr)))
        checks.append({'group':group,'parameters':params,'passed':True})
    numerators={}
    for p in range(6):
        for q in range(6-p):
            r=p+q
            N=cut(A*P(r,u+v)-P(p,u)*P(r,v)-P(q,v)*P(r,u)+P(p,u)*P(q,v),max_degree)
            numerators[p,q]=N
            check('axis_divisibility',{'p':p,'q':q},N.subs(u,0)+N.subs(v,0))
            H=lambda n:s.harmonic(n)
            closed=(-1)**p*(s.pi**2/3-s.harmonic(r,2)+(H(r)-H(p))*(H(r)-H(q)))
            actual=(-1)**p*N.coeff(u,1).coeff(v,1)
            check('polygamma_contact',{'p':p,'q':q},actual-closed)
            for m in range(6):
                for n in range(6-m):
                    delta=s.expand((-1)**(m+n+p)*s.factorial(m)*s.factorial(n)*N.coeff(u,m+1).coeff(v,n+1))
                    formulas.append({'p':p,'q':q,'m':m,'n':n,'delta':str(delta),'latex':s.latex(delta)})
    for row in formulas:
        p,q,m,n=[row[k] for k in ['p','q','m','n']]
        rev=(-1)**(m+n+q)*s.factorial(m)*s.factorial(n)*numerators[q,p].coeff(u,n+1).coeff(v,m+1)
        check('reflection_symmetry',{'p':p,'q':q,'m':m,'n':n},s.sympify(row['delta'])-(-1)**(p+q)*rev)
        if m>=p+q or n>=p+q:
            baseline=(-1)**(m+n)*s.factorial(m)*s.factorial(n)*numerators[0,p+q].coeff(u,m+1).coeff(v,n+1)
            check('split_stabilization',{'p':p,'q':q,'m':m,'n':n},s.sympify(row['delta'])-(-1)**p*baseline)
    for p in range(11):
        for m in range(11):
            # Direct summation of the local integration-by-parts anomalies.
            actual=sum(P(j,u).coeff(u,m)/s.Integer(j+1) for j in range(p))
            expected=P(p,u).coeff(u,m+1)
            check('derivative_contact_telescope',{'p':p,'m':m},actual-expected)
    for m in range(6):
        expected=s.factorial(m)*s.zeta(m+2)*(3-s.Rational(1,2)**m if m%2==0 else 1)
        actual=(-1)**m*s.factorial(m)*A.coeff(u,m+1).coeff(v,1)
        check('one_edge_parity',{'m':m},actual-expected)
    # Independent symbolic Fourier multiplication, not just re-extracting the contact numerator.
    deg=5; E=E_series(deg); Es=E.xreplace({u:v,v:u}); AA=A_series(deg)
    gm=gamma_series(-s.I*s.pi/2,deg);gp=gamma_series(s.I*s.pi/2,deg)
    x=gm.gen
    gm_u=gm.as_expr().subs(x,u);gp_v=gp.as_expr().subs(x,v)
    for p in range(4):
        for q in range(4-p):
            r=p+q
            trp=s.Poly(s.expand(P(r,x)-gp.as_expr()),x)
            trm=s.Poly(s.expand(P(r,x)-gm.as_expr()),x)
            tp=s.Add(*[c*x**(ij[0]-1) for ij,c in trp.terms() if ij[0]>=1])
            tm=s.Add(*[c*x**(ij[0]-1) for ij,c in trm.terms() if ij[0]>=1])
            conv=cut((P(p,u)-gm_u)*(P(q,v)-gp_v),deg)
            J=cut(v*(P(p,u)*tp.subs(x,v)-E*tp.subs(x,u+v))
                  +u*(P(q,v)*tm.subs(x,u)-Es*tm.subs(x,u+v)),deg)
            NN=cut(AA*P(r,u+v)-P(p,u)*P(r,v)-P(q,v)*P(r,u)+P(p,u)*P(q,v),deg)
            diff=s.expand(conv-J-NN)
            for m in range(4):
                for n in range(4-m):
                    check('independent_fourier_contact',{'p':p,'q':q,'m':m,'n':n},
                          diff.coeff(u,m+1).coeff(v,n+1))
    for M in range(1,9):
        for d in range(1,M):
            S=sum((-1)**j*s.binomial(2*M,M+j)*j**(2*d) for j in range(1,M+1))
            check('trigonometric_resonance_zero',{'M':M,'d':d},S)
    counts={}
    for row in checks:counts[row['group']]=counts.get(row['group'],0)+1
    report={'status':'PASS','python':platform.python_version(),'sympy':s.__version__,
            'check_count':len(checks),'groups':counts,'contact_formula_count':len(formulas),
            'scope':{'p_plus_q_max':5,'m_plus_n_max':5,'independent_fourier_maxima':3},
            'note':'Finite exact symbolic checks, not proof-assistant verification.','checks':checks}
    (ROOT/'data'/'exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'data'/'contact_coefficients.json').write_text(json.dumps(formulas,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':main()
