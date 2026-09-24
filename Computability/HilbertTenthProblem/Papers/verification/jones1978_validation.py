#!/usr/bin/env python3
"""Exact structural checks and finite regressions for the corrected Jones edition.

Run: python jones1978_validation.py
Reads the current source.
Requires SymPy. This is not a formal verification of the universality theorem.
"""
from __future__ import annotations
import json
import math
from functools import lru_cache
from pathlib import Path
import sympy as S


def main() -> None:
    names = ('x n u v alpha theta beta h rho gamma z r psi t e s q varphi '
             'p b w phi g pi omega fp gp hp ip jp sigma delta eta '
             'qp ap rp bp sp cp tp dp up ep zeta epsilon chi y xi '
             'kp lp mp np pp mu kappa nu lam upsilon c iota k l a m d f i j tau')
    V = dict(zip(names.split(), S.symbols(names)))
    (x,n,u,v,alpha,theta,beta,h,rho,gamma,z,r,psi,t,e,s,q,varphi,
     p,b,w,phi,g,pi,omega,fp,gp,hp,ip,jp,sigma,delta,eta,
     qp,ap,rp,bp,sp,cp,tp,dp,up,ep,zeta,epsilon,chi,y,xi,
     kp,lp,mp,np,pp,mu,kappa,nu,lam,upsilon,c,iota,k,l,a,m,d,f,i,j,tau) = V.values()
    M = 1+beta+r*beta
    A = (3*(s+w)**2+9*w+3*s-2*r)**2 + (
        M**2*(1+(alpha-t-p)**2)*(beta-t**2-p**2)
        -(alpha-t-p)**2-(g+1)*M**2)**2
    B = (3*(s+w)**2+9*w+3*s+2-2*r)**2 + (
        M**2*(1+(alpha-t*p)**2)*(beta-t**2-p**2)
        -(alpha-t*p)**2-(g+1)*M**2)**2
    equations = [
        2*n-(u+v)**2-3*v-u,
        alpha-theta*beta-theta,
        h+h*beta+h*beta*v-x-rho-rho*beta-rho*beta*u,
        (h+h*beta+h*beta*v-alpha)**2+x**2+gamma+1-beta,
        z-3*n-alpha**3,
        z**18*(z**6+2)*(r+1)**2+1-psi**2,
        t+e+e*beta+e*beta*s-alpha-q*varphi,
        p+b+b*beta+b*beta*w-alpha-q*phi,
        A*B*(3*g+2-r)*(3*n+g-r)-q*pi,
        omega-r-q-b-e-g-s-w-fp-gp-hp-ip-jp,
        omega**3*(omega+2)*(sigma+1)**2+1-delta**2,
        eta-sigma*r-sigma,
        eta-b-(qp+sigma)*ap,
        eta-e-(rp+sigma)*bp,
        eta-g-(sp+sigma)*cp,
        eta-s-(tp+sigma)*dp,
        eta-w-(up+sigma)*ep,
        eta**3*(eta+2)*(zeta+1)**2+1-epsilon**2,
        chi-zeta*(eta-r)*(qp+sigma)*(rp+sigma)*(sp+sigma)*(tp+sigma)*(up+sigma),
        y-q-(1+xi)*(eta-r),
        y-q*fp-(qp+sigma)*kp,
        y-q*gp-(rp+sigma)*lp,
        y-q*hp-(sp+sigma)*mp,
        y-q*ip-(tp+sigma)*np,
        y-q*jp-(up+sigma)*pp,
        (mu**2-1)*kappa**2+1-nu**2,
        (mu**2*chi**2-1)*lam**2+1-upsilon**2,
        5*(c-kappa*lam*y)**2+iota-kappa**2*lam**2,
        mu-9*eta*chi*y,
        kappa-eta+z-1-k*(mu-1),
        lam-z-1-l*(mu*chi-1),
        a-mu*chi-mu,
        c-m-eta-1,
        d**2-(a**2-1)*c**2-1,
        f**2-4*(a**2-1)*i**2*c**4-1,
        (d+tau*f)**2-((a+f**2*(f**2-a))**2-1)*(eta+1+2*j*c)**2-1,
    ]
    assert len(equations) == 36
    unknowns = set().union(*(eq.free_symbols for eq in equations)) - {x,n}
    assert len(unknowns) == 67, len(unknowns)

    @lru_cache(maxsize=None)
    def structural_degree(expr: S.Expr) -> int:
        """Polynomial degree upper bound, treating x,n as parameters.
        Checks integer polynomial syntax without multivariate expansion.
        """
        if expr.is_Integer:
            return 0
        if expr.is_Symbol:
            return int(expr in unknowns)
        if expr.is_Add:
            return max(map(structural_degree, expr.args))
        if expr.is_Mul:
            return sum(map(structural_degree, expr.args))
        if expr.is_Pow and expr.exp.is_Integer and expr.exp >= 0:
            return int(expr.exp)*structural_degree(expr.base)
        raise AssertionError(f'Not integer-polynomial syntax: {expr!r}')

    # The upper bound is exact when an integer line specialization attains it.
    # This avoids a huge and unnecessary full multivariate expansion of row 9.
    degrees = []
    zline = S.Symbol('zline')
    for idx, eq in enumerate(equations, 1):
        bound = structural_degree(eq)
        ordered = sorted(unknowns, key=str)
        substitution = {sym: (j+1)*zline for j,sym in enumerate(ordered)}
        substitution.update({x:S.Integer(2),n:S.Integer(3)})
        line = S.Poly(eq.xreplace(substitution), zline)
        assert line.degree() == bound, (idx,line.degree(),bound)
        degrees.append(bound)
    assert max(degrees) == 38 and degrees[8] == 38
    # Over R, leading homogeneous parts squared cannot cancel each other.
    sum_of_squares_degree = 2*max(degrees)
    assert sum_of_squares_degree == 76

    # Cantor pairing; the key index mismatch is J(0,2)=5.
    def pairing(s0:int,w0:int) -> int:
        return ((s0+w0)**2+3*w0+s0)//2
    assert pairing(0,2) == 5
    pairs = {pairing(s0,w0):(s0,w0) for s0 in range(31) for w0 in range(31)}
    assert len(pairs)==31**2
    for n0 in range(100):
        s0,w0=pairs[n0]
        assert s0<=n0 and w0<=n0
    # P0=0, P2=X0: X0=-x solves W5 for every tested x>0;
    # 0=X0+x has no nonnegative X0 for any x>0, by positivity.
    assert all((-x0)+x0 == 0 for x0 in range(1,100))

    count_lemma = 0
    for uu in range(-9,10):
        if uu==0: continue
        for vv in range(-15,16):
            for ww in range(-3,8):
                numerator=uu*uu*(1+vv*vv)*ww-vv*vv-uu*uu
                t_exists=numerator>=0 and numerator%(uu*uu)==0
                assert t_exists == (vv%uu==0 and ww>0)
                count_lemma += 1

    count_divisibility=0
    for mm in range(1,15):
        for ff in range(1,15):
            if math.gcd(mm,ff)!=1: continue
            for qq in range(-12,13):
                for hh in range(-12,13):
                    combined=(mm*mm*hh+ff*qq*qq)%(ff*mm*mm)==0
                    separate=hh%ff==0 and qq%mm==0
                    assert combined==separate
                    count_divisibility+=1
    mm,ff,qq,hh=9,163,3,1304
    assert math.gcd(mm,ff)==1 and ff%81==1
    assert (mm*hh+ff*qq*qq)%(ff*mm*mm)==0 and qq%mm!=0
    assert (mm*mm*hh+ff*qq*qq)%(ff*mm*mm)!=0

    count_binomial=0
    for zz in range(0,8):
        for dd in range(1,25):
            modulus=dd//math.gcd(dd,math.factorial(zz))
            for aa in range(0,25):
                bb=aa+dd
                assert (math.comb(aa,zz)-math.comb(bb,zz))%modulus==0
                count_binomial+=1
    for zz in range(1,8):
        rr=2*math.factorial(zz)**2-1
        factors=[(rr+1)//jj-1 for jj in range(1,zz+1)]
        assert math.prod(factors)==math.comb(rr,zz)
        assert all(math.gcd(fi,fj)==1 for i0,fi in enumerate(factors)
                   for fj in factors[i0+1:])
    assert 30**13 > 2*10**13  # Sufficient crude majorant margin.

    article=(Path(__file__).resolve().parents[1]/'1978'/'jones1978_corrected.tex').read_text(encoding='utf-8')
    assert article.count(r'\label{sys:')==36
    assert article.count(r'\bibitem{')==27
    assert r'\includegraphics' not in article and r'\begin{verbatim}' not in article
    assert not any(ord(ch)<32 and ch not in '\n\r' for ch in article)
    result={
        'scope':'Exact polynomial degree/count checks plus finite regressions; not a formal proof of universality.',
        'sympy_version':S.__version__,
        'equations':36,'parameters':['x','n'],'unknown_count':len(unknowns),
        'unknowns_ascii':sorted(map(str,unknowns)),
        'prime_variable_convention':'ap means a-prime, ..., up means u-prime; lam means lambda.',
        'degrees_in_equation_order':degrees,'maximum_degree':max(degrees),
        'sum_of_squares_degree':sum_of_squares_degree,
        'lemma_2_2_finite_cases':count_lemma,
        'corrected_divisibility_finite_cases':count_divisibility,
        'lemma_2_5_finite_cases':count_binomial,
        'bibliography_entries':27,
        'status':'PASS'
    }
    target=Path(__file__).resolve().with_name('jones1978_validation_results.json')
    target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
