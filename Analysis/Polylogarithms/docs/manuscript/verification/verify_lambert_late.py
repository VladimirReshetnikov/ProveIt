"""Finite exact correction compiler and independent-coefficient diagnostics.
The uniform theorem is proved in 01-lambert-late-coefficients.tex.
"""
from pathlib import Path
import json, sympy as s, mpmath as mp
B=Path(__file__).resolve().parents[1]
V=B/'verification'
J=4
L,u,A,z,w=s.symbols('L u A z w')
def falling(x,n):return s.prod(x-i for i in range(n))
def rising(x,n):return s.prod(x+i for i in range(n))
def r(m):
    return s.Rational(-1,4) if m==1 else (-1)**m*s.zeta(1-m)**2/s.factorial(m)
S=[s.Integer(0)]+[s.summation(s.Symbol('i')**i,(s.Symbol('i'),1,L)) for i in range(1,J+1)]
B=[s.Integer(1)]
for j in range(1,J+1):
    B.append(s.expand(sum((L**i+S[i])*B[j-i] for i in range(1,j+1))/j))
touch=[s.Integer(1)]
for j in range(2*J+1):touch.append(s.expand(z*(touch[-1]+s.diff(touch[-1],z))))
def poisson(p):
    p=s.Poly(s.expand(p),L)
    return s.expand(sum(coef*touch[pow[0]] for pow,coef in p.terms()))
def multisets(budget,m=2):
    if m>budget+1:
        yield {}
        return
    for count in range(budget//(m-1)+1):
        for other in multisets(budget-count*(m-1),m+1):
            yield {**other,**({m:count} if count else {})}
polys=[]
for j in range(J+1):
    p=0
    for counts in multisets(j):
        h=sum(counts.values());total=sum(m*a for m,a in counts.items());d=total-h
        weight=u**h*A**total*s.prod(r(m)**a/s.factorial(a) for m,a in counts.items())
        if not weight:continue
        degree=j-d;k=L+h+1
        f=0
        for v in range(degree+1):
            hv=falling(k-1,v)*rising(k,v)*(u/2)**v/s.factorial(v)
            f+=B[degree-v].subs(L,L+total)*hv
        # epsilon=+1; epsilon=-1 is obtained by A -> -A.
        p+=weight*poisson(f).subs(z,-A*u/4)
    p=s.factor(p);polys.append(p)
    print('T',j,':',p,flush=True)
theta=A*u/4;zz=u*A*A/288
p1=(1+u)*theta**2/2+zz
p2=(1+u)**2*theta**4/8+(3*u*u+11*u+11+(u+1)*zz)*theta**2/2+(u+5)*zz+zz*zz/2
d2=(6*u*u+15*u+10)*theta**2/6+(2*u+4)*zz+2*u+3
assert polys[0]==1
assert s.expand(polys[1]-(p1-(u+2)*theta))==0
assert s.expand(polys[2]-(p2-theta*d2))==0
# Finite exact product checks of the Faulhaber/gamma coordinate.
checks=0
for ell in range(0,13):
    product=s.Integer(1)
    for i in [ell,*range(1,ell+1)]:
        product=s.series(product*sum((i*w)**j for j in range(J+1)),w,0,J+1).removeO()
    for j in range(J+1):
        assert s.expand(product).coeff(w,j)==B[j].subs(L,ell)
        checks+=1
data=json.loads((V/'lambert-late-finite-coefficients.json').read_text())
mp.mp.dps=50
fun=[s.lambdify((u,A),p,'mpmath') for p in polys]
rows=[]
def dec(v):return mp.mpc(v['real'],v['imag'])
for row in data['rows']:
    n=row['n'];uu=dec(row['u']);aa=4*mp.pi**2;actual=dec(row['D_n'])
    terms=[-uu*(mp.exp(-aa*uu/4)*f(uu,aa)+(-1)**n*mp.exp(aa*uu/4)*f(uu,-aa))/2 for f in fun]
    partial=mp.mpc(0);errors=[]
    for j,t in enumerate(terms):
        partial+=t/n**j
        errors.append(str(abs(actual-partial)))
    rows.append(dict(n=n,u=row['u'],absolute_errors=errors))
out=dict(scope='Derived finite all-order correction compiler; exact identities and diagnostic comparison only. Uniform infinite theorem is supplied separately by the written proof.',maximum_correction=J,
         exact_faulhaber_product_checks=checks,first_two_corrections_match=True,passed=True,imports_delivered_code=False,
         positive_action_polynomials=[str(p) for p in polys],diagnostics=rows)
(V/'lambert-late-checks.json').write_text(json.dumps(out,indent=2))
for row in rows:
    if row['n'] in (200,201):print(row,flush=True)
