#!/usr/bin/env python3
"""Exact finite-jet engine for coincident Stieltjes moments.

All coefficients are symbolic rational expressions in pi, odd zeta values,
Stieltjes constants g_j, and spectral zeta derivatives zd_r_j at r+1.
Finite checks support (and do not replace) the analytic proofs in article.tex.
"""
from __future__ import annotations
import argparse, json, math
from functools import lru_cache
from pathlib import Path
import sympy as sp

u, v, L = sp.symbols('u v L')
Poly = dict[tuple[int, int], sp.Expr]

def add(a: Poly, b: Poly) -> Poly:
    c = dict(a)
    for ij, x in b.items(): c[ij] = c.get(ij, 0) + x
    return {ij: sp.expand(x) for ij, x in c.items() if x != 0}

def scale(a: Poly, c: sp.Expr) -> Poly:
    return {ij: sp.expand(c*x) for ij, x in a.items() if c*x != 0}

def mul(a: Poly, b: Poly, d: int) -> Poly:
    out: Poly = {}
    for (i,j), x in a.items():
        for (k,l), y in b.items():
            if i+j+k+l <= d:
                ij = (i+k,j+l); out[ij] = out.get(ij,0)+x*y
    return {ij: sp.expand(x) for ij,x in out.items() if x != 0}

def exp_poly(a: Poly, d: int) -> Poly:
    assert a.get((0,0),0) == 0
    out: Poly = {(0,0):sp.Integer(1)}; power = out
    for n in range(1, d+1):
        power = mul(power, a, d)
        if not power: break
        out = add(out, scale(power, 1/sp.factorial(n)))
    return out

def diag(coeff: list[sp.Expr], d: int) -> Poly:
    return {(i,k-i):sp.binomial(k,i)*c for k,c in enumerate(coeff[:d+1])
            for i in range(k+1) if c != 0}

def swap(a: Poly) -> Poly: return {(j,i):x for (i,j),x in a.items()}

def univ_log_e(d: int) -> Poly:
    out = {}
    for k in range(2,d+1):
        for i in range(k+1):
            c = int(i==k)+(-1)**k*(sp.binomial(k,i)-int(i==0))
            if c: out[(i,k-i)] = c*sp.zeta(k)/k
    return out

def univ_log_a(d: int) -> Poly:
    out = {}
    for k in range(2,d+1):
        for i in range(k+1):
            c = sp.Rational(int(i==0)+int(i==k)-sp.binomial(k,i), k)
            if k%2==0:
                c -= (1-sp.Rational(1,2)**k)*sp.Rational(2,k)*sp.binomial(k,i)*((-1)**(k-i)-1)
            if c: out[(i,k-i)] = c*sp.zeta(k)
    return out

@lru_cache(None)
def poch_coeff(p: int) -> tuple[sp.Expr,...]:
    if p < 0: raise ValueError('p must be nonnegative')
    pol = sp.Poly(sp.prod(1+u/sp.Integer(j) for j in range(1,p+1)),u)
    return tuple(pol.nth(k) for k in range(p+1))

def pc(p: int,k: int) -> sp.Expr:
    return poch_coeff(p)[k] if 0 <= k <= p else sp.Integer(0)

def zsym(r: int,j: int) -> sp.Expr:
    return sp.Symbol(f'zd_{r}_{j}')

def gsym(j: int) -> sp.Expr: return sp.Symbol(f'g_{j}')

@lru_cache(None)
def gamma_derivative(m: int,k: int) -> sp.Expr:
    if k==0: return gsym(m)
    return sp.expand((-1)**(m+k)*sp.factorial(m)*sp.factorial(k)*
        sum(pc(k,m-j)*zsym(k,j)/sp.factorial(j) for j in range(m+1)))

class Engine:
    def __init__(self, d: int = 8):
        self.d=d
        self.E=exp_poly(univ_log_e(d),d)
        self.ES=swap(self.E)
        self.A=exp_poly(univ_log_a(d),d)
        zc=[sp.Integer(1)]+[(-1)**j*gsym(j)/sp.factorial(j) for j in range(d)]
        self.AZ=mul(self.A,diag(zc,d),d)
        self.wcache={}
        self.scache={}

    def w(self,r: int):
        if r not in self.wcache:
            co=[]
            for k in range(self.d+1):
                co.append(sp.expand(sp.factorial(r)*sum(pc(r,k-j)*zsym(r,j)/sp.factorial(j) for j in range(k+1))))
            dw=diag(co,self.d)
            self.wcache[r]=(co,mul(self.E,dw,self.d),mul(self.ES,dw,self.d))
        return self.wcache[r]

    def moment(self,p:int,q:int,m:int,n:int)->sp.Expr:
        if min(p,q,m,n)<0: raise ValueError('all indices must be nonnegative')
        if m+n+2>self.d: raise ValueError('increase truncation degree')
        r=p+q; f=(-1)**(m+n)*sp.factorial(m)*sp.factorial(n)
        if r==0:
            return sp.expand(-f*self.AZ.get((m+1,n+1),0))
        co,ew,esw=self.w(r)
        ans=(-1)**q*(pc(p,m+1)*co[n]-ew.get((m+1,n),0))
        ans+=(-1)**p*(pc(q,n+1)*co[m]-esw.get((m,n+1),0))
        return sp.expand(f*ans)

    def singular(self,p:int,q:int,m:int,n:int)->sp.Expr:
        r=p+q
        if r not in self.scache:
            # (1+w)_r exp(-L w), then multiplication by E.
            co=[sp.expand(sp.factorial(r)*sum(pc(r,k-j)*(-L)**j/sp.factorial(j) for j in range(k+1))) for k in range(self.d+1)]
            self.scache[r]=(co,mul(self.E,diag(co,self.d),self.d))
        co,ew=self.scache[r]
        f=(-1)**(m+n+q)*sp.factorial(m)*sp.factorial(n)
        return sp.expand(f*(pc(p,m+1)*co[n]-ew.get((m+1,n),0)))

    def boundary(self,p:int,q:int,m:int,n:int)->sp.Expr:
        tm=(-1)**(m+p)*sp.factorial(m)*sp.factorial(p)*pc(p,m)
        tn=(-1)**(n+q)*sp.factorial(n)*sp.factorial(q)*pc(q,n)
        r=p+q+1
        return sp.expand(-tm*gamma_derivative(n,r)/sp.factorial(p+1)-tn*gamma_derivative(m,r)/sp.factorial(q+1))

def main():
    if not __debug__: raise RuntimeError("Run without -O: this verifier uses assertions.")
    ap=argparse.ArgumentParser();ap.add_argument('--spectral-total',type=int,default=4)
    ap.add_argument('--derivative-total',type=int,default=6);ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data');args=ap.parse_args()
    if not 0<=args.spectral_total<=8 or not 0<=args.derivative_total<=12: raise ValueError('unsupported check budget')
    d=args.spectral_total+2; eng=Engine(d); rows=[]; singular=[]; checks={}
    count_sym=count_ibp=count_top=0
    for r in range(args.derivative_total+1):
        for p in range(r+1):
            q=r-p
            for N in range(args.spectral_total+1):
                for m in range(N+1):
                    n=N-m; expr=eng.moment(p,q,m,n)
                    assert sp.expand(expr-eng.moment(q,p,n,m))==0
                    count_sym+=1
                    if r:
                        expected=(-1)**(N+1)*sp.factorial(r)*(
                            sp.Rational((-1)**p,n+1)+sp.Rational((-1)**q,m+1))
                        assert sp.expand(expr.coeff(zsym(r,N+1))-expected)==0
                    else:
                        expected=sp.Rational(N+2,(m+1)*(n+1))
                        assert sp.expand(expr.coeff(gsym(N+1))-expected)==0
                        assert expr.coeff(gsym(N))==0
                    count_top+=1
                    rows.append(dict(p=p,q=q,m=m,n=n,expression=str(expr),latex=sp.latex(expr)))
                    se=eng.singular(p,q,m,n)
                    assert sp.Poly(se,L).degree()<=N+1
                    singular.append(dict(p=p,q=q,m=m,n=n,polynomial=str(se),latex=sp.latex(se)))
                    if r<args.derivative_total:
                        b=eng.boundary(p,q,m,n)
                        assert sp.expand(eng.moment(p+1,q,m,n)+eng.moment(p,q+1,m,n)-b)==0,(p,q,m,n)
                        count_ibp+=1
    count_parity=0
    for r in range(1,args.derivative_total+1):
        for p in range(r+1):
            q=r-p
            if r%2==0:
                expect=(-1)**p*sp.factorial(r)*((sp.harmonic(p)+sp.harmonic(q)-2*sp.harmonic(r))*zsym(r,0)-2*zsym(r,1))
            else:
                expect=(-1)**p*sp.factorial(r)*(sp.harmonic(q)-sp.harmonic(p))*zsym(r,0)
            assert sp.expand(eng.moment(p,q,0,0)-expect)==0
            se=(-1)**q*sp.factorial(r)*(L+sp.harmonic(p)-sp.harmonic(r))
            assert sp.expand(eng.singular(p,q,0,0)-se)==0
            count_parity+=1
    # Independent low-weight, human-readable targets.
    expected00=2*gsym(1)-2*sp.zeta(2)
    expected10=sp.Rational(3,2)*gsym(2)+2*gsym(0)*sp.zeta(2)-sp.zeta(3)
    expected11=gsym(3)+4*sp.zeta(2)*gsym(1)+2*sp.zeta(3)*gsym(0)-sp.Rational(7,2)*sp.zeta(4)
    expected20=sp.Rational(4,3)*gsym(3)+4*sp.zeta(2)*gsym(1)+2*sp.zeta(3)*gsym(0)-sp.Rational(11,2)*sp.zeta(4)
    explicit_targets=0
    for m,n,x in [(0,0,expected00),(1,0,expected10),(1,1,expected11),(2,0,expected20)]:
        if m+n<=args.spectral_total:
            assert sp.expand(eng.moment(0,0,m,n)-x)==0
            explicit_targets+=1
    # Normalized Pochhammer coefficients from generalized harmonic numbers.
    harmonic_checks=0
    t=sp.Symbol('t')
    for p in range(args.derivative_total+1):
        h=sum((-1)**(j+1)*sp.harmonic(p,j)*t**j/j for j in range(1,5))
        got=sp.series(sp.exp(h),t,0,5).removeO().expand()
        for j in range(5): assert got.coeff(t,j)==pc(p,j); harmonic_checks+=1
    checks.update(symmetry=count_sym,integration_by_parts=count_ibp,highest_jet=count_top,
                  parity=count_parity,singular_degree=len(singular),harmonic=harmonic_checks,explicit_targets=explicit_targets)
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'exact_moments.json').write_text(json.dumps({'notation':'g_j = gamma_j(1); zd_r_j = d^j/ds^j zeta(s) at s=r+1','rows':rows},indent=2)+'\n')
    (args.output/'collision_polynomials.json').write_text(json.dumps({'notation':'J = a^(-p-q-1) polynomial(log(a)) + analytic remainder','rows':singular},indent=2)+'\n')
    result=dict(status='passed',moment_count=len(rows),polynomial_count=len(singular),checks=checks,total_checks=sum(checks.values()),sympy=sp.__version__,degree=d)
    (args.output/'exact_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
