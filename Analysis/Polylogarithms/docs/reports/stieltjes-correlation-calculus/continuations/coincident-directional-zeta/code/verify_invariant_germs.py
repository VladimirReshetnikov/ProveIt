#!/usr/bin/env python3
"""Exact finite checks of the coordinate-invariant logarithmic-germ theorem.

The proof in invariant_germs.tex is all-order.  These checks use rational
polynomials, compare the residue and binomial constructions, and verify
independence of the finite obstruction maps.  No numeric equality search.
"""
import json
from pathlib import Path
import sympy as s

z,t,a,b = s.symbols('z t a b')
checks=[]

def binom_poly(x,k):
    return s.expand(s.prod(x-j for j in range(k))/s.factorial(k))

def defect_binomial(q,n,d):
    out={}
    for k in range(1,(q-1)//d+1):
        j=q-1-d*k
        v=s.factorial(n)*(-1)**j/s.factorial(j)*s.expand(binom_poly(z-q,k)).coeff(z,n+1)
        if v:
            out[(j,k)]=s.factor(v)
    return out

def defect_residue(q,n,d):
    # Expand the residue formula directly, without using a z-regulator.
    H=1+a*t**d
    L=s.series(s.log(H),t,0,q).removeO()
    R=s.series(H**(-q)*L**(n+1)/s.Integer(n+1),t,0,q).removeO().expand()
    out={}
    for j in range(q):
        v=s.expand(R.coeff(t,q-1-j)*(-1)**j/s.factorial(j))
        for k in range(q):
            c=v.coeff(a,k)
            if c:
                out[(j,k)]=s.factor(c)
    return out

for q in range(1,8):
  for n in range(q+1):
    for d in range(1,5):
      x=defect_binomial(q,n,d)
      y=defect_residue(q,n,d)
      assert x==y,(q,n,d,x,y)
      checks.append({'test':'independent_residue','q':q,'n':n,'d':d,'pass':True})

rank_results=[]
for R in range(1,10):
  for d in range(1,5):
    columns=[(q,n) for q in range(1,R+1) for n in range((q-1)//d)]
    rows=sorted({row for q,n in columns for row in defect_binomial(q,n,d)})
    M=s.Matrix([[defect_binomial(q,n,d).get(row,0) for q,n in columns] for row in rows])
    rank=M.rank() if columns else 0
    expected=sum((q-1)//d for q in range(1,R+1))
    assert rank==expected==len(columns)
    rank_results.append({'pole_order':R,'flatness':d,'rank':rank,'expected':expected})

threshold_results=[]
for r in range(1,9):
  for d in range(1,6):
    E=s.prod(1-z/s.Integer(j) for j in range(1,r+1))
    for n in range(0,2*r+2):
      singular=s.Poly(s.expand((-1)**r*s.factorial(r)*s.factorial(n)*sum(s.expand(E).coeff(z,k)*t**(n-k)/s.factorial(n-k) for k in range(min(n,r)+1))),t)
      defect={}
      for (ell,),c in singular.terms():
        for key,v in defect_binomial(r+1,ell,d).items():
          defect[key]=s.expand(defect.get(key,0)+c*v)
      defect={key:v for key,v in defect.items() if v!=0}
      expected=(d>=r+1 or n>=r+r//d)
      assert (not defect)==expected,(r,n,d,defect)
      if d<=r and n==r+r//d-1:
        K=r//d; e=r-d*K
        target={(e,K):(-1)**e*s.factorial(n)/(s.factorial(e)*s.factorial(K))}
        assert defect==target,(r,n,d,defect,target)
      threshold_results.append({'r':r,'n':n,'d':d,'zero':not bool(defect),'criterion':expected})

# Small examples from the text.  They retain a general cubic coordinate jet.
H=1+a*t+b*t*t
examples={}
for q,n in [(2,0),(3,0),(3,1),(4,2)]:
  L=s.series(s.log(H),t,0,q).removeO()
  R=s.series(H**(-q)*L**(n+1)/s.Integer(n+1),t,0,q).removeO().expand()
  terms={str(j):str(s.factor((-1)**j/s.factorial(j)*R.coeff(t,q-1-j))) for j in range(q) if R.coeff(t,q-1-j)!=0}
  examples[f'q={q},n={n}']=terms
assert examples['q=2,n=0']=={'0':'a'}
assert s.simplify(s.sympify(examples['q=3,n=0']['0'])-(b-s.Rational(7,2)*a*a))==0
assert examples['q=3,n=0']['1']=='-a'
assert s.simplify(s.sympify(examples['q=3,n=1']['0'])-a*a/2)==0

result={'proof_status':'All-order proof in invariant_germs.tex; exact finite audits only here.',
        'sympy_version':s.__version__,
        'independent_residue_checks':len(checks),
        'obstruction_ranks':rank_results,
        'stieltjes_threshold_checks':len(threshold_results),
        'examples_delta_coefficients':examples,
        'all_passed':True}
p=(Path(__file__).resolve().parents[1]/'results'/'invariant_germs_verification.json')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'all_passed':True,'independent_residue_checks':len(checks),'rank_checks':len(rank_results),'stieltjes_threshold_checks':len(threshold_results),'output':str(p)}))
