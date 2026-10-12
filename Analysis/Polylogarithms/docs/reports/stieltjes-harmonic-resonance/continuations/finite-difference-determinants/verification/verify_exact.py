#!/usr/bin/env python3
"""Replay finite exact identities. No numerical relation search is used."""
from __future__ import annotations
import json, sys, time
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import sympy as S
from core import (endpoint, weight, endpoint_matrix, uv, finite_moment,
                  boundary_moment, partition_direct, harmonic_matrices,
                  stencil_residues, rank_one_type, complete_bell)
ROOT=Path(__file__).resolve().parents[1]
counts=Counter(); start=time.time(); examples=[]
def eq(lhs,rhs,family):
    if isinstance(lhs,S.MatrixBase): ok=(lhs-rhs).applyfunc(S.cancel)==S.zeros(lhs.rows,lhs.cols)
    else: ok=S.cancel(lhs-rhs)==0
    if not ok: raise AssertionError((family,lhs,rhs,S.cancel(lhs-rhs)))
    counts[family]+=1

def yes(value,family):
    if not value: raise AssertionError(family)
    counts[family]+=1

# Moment identities including the empty and overlapping-endpoint cutoffs.
for r in range(2,6):
 for a in (S.Integer(1),S.Rational(2,3)):
  for s in (S.Integer(1),S.Integer(2),S.Integer(4)):
   for N in (0,1,3,7):
    for k in range(2*r-1):
     eq(finite_moment(r,k,N,a,s),boundary_moment(r,k,N,a,s),'finite_boundary_moments')

# Cauchy--Binet against explicit ordered tuples, not another determinant.
for r in range(2,5):
 for N in (r-2,r-1,r+2):
  for a,s in ((S.Integer(1),S.Integer(2)),(S.Rational(3,2),S.Integer(3))):
   mat=S.Matrix(r,r,lambda i,j: finite_moment(r,i+j,N,a,s))
   eq(mat.det(),partition_direct(r,N,a,s),'ordered_partition_determinants')

# Exact Gamma-product residue and listed examples.
for r in range(2,8):
 for a in (S.Integer(1),S.Rational(3,2),S.Integer(3)):
  U,V=uv(r,a,S.Integer(1))
  product=S.prod(S.factorial(j)*S.gamma(a+j)*S.gamma(1+j)*S.gamma(r-j)/
       (S.gamma(2*r-1-j)*S.gamma(a+2*r-2-j)) for j in range(r-1))
  eq(S.simplify(V/product),1,'residue_gamma_product')
for r in range(2,5):
 for s in range(1,5):
  U,V=uv(r,S.Integer(1),S.Integer(s))
  examples.append({'r':r,'s':s,'U':str(U),'V':str(V)})
  # Matrix determinant lemma with a genuinely independent zeta symbol.
  Z=S.Symbol('Z'); mat=endpoint_matrix(r,S.Integer(1),S.Integer(s));mat[-1,-1]+=Z
  eq(mat.det(),U+V*Z,'single_zeta_algebra')

# Finite cutoff polarization with independent orders AND independent shifts.
for r in (2,3):
 N=r+1;ts=S.symbols('t:'+str(r));pars=[(S.Rational(j+2,j+1),S.Integer(j+2)) for j in range(r)]
 mat=S.zeros(r)
 for t,(a,s) in zip(ts,pars):
  mat+=t*S.Matrix(r,r,lambda i,j:finite_moment(r,i+j,N,a,s))
 coeff=S.Poly(mat.det(),*ts).coeff_monomial(S.prod(ts))/S.factorial(r)
 direct=0
 for ns in combinations(range(N+1),r):
  vand=S.prod((ns[j]-ns[i])**2 for i in range(r) for j in range(i+1,r))
  direct+=vand*sum(S.prod(weight(r,ns[i],*pars[sigma[i]]) for i in range(r))
                   for sigma in permutations(range(r)))/S.factorial(r)
 eq(coeff,direct,'independent_order_shift_polarization')
 es=sum((t*endpoint_matrix(r,a,s) for t,(a,s) in zip(ts,pars)),S.zeros(r))
 zs=S.symbols('Z:'+str(r)); mm=es.copy();mm[-1,-1]+=sum(t*z for t,z in zip(ts,zs))
 rhs=es.det()+sum(t*z for t,z in zip(ts,zs))*es[:-1,:-1].det()
 eq(mm.det(),rhs,'no_mixed_zeta_products')

# Bell-polynomial and Gamma/harmonic identity without special-function numerics.
for r in range(2,6):
 d=2*r-2
 for a in (S.Integer(1),S.Rational(4,3)):
  for n in (0,2,6):
   for m in range(1,7):
    hs=[sum((n+a+j)**(-q) for j in range(d+1)) for q in range(1,m)]
    bell=complete_bell([S.factorial(q-1)*h for q,h in enumerate(hs,1)])
    rhs=bell/(S.factorial(m-1)*S.prod(n+a+j for j in range(d+1)))
    eq(weight(r,n,a,S.Integer(m)),rhs,'gamma_harmonic_bell')

# Repeated-pole classification and exact finite-difference inversion.
z=S.symbols('z');x=S.symbols('x')
for r in range(2,7):
 d=2*r-2
 for maxh in range(1,5):
  seeds={(0,1):S.Rational(2,3)}
  for h in range(2,maxh+1):
   seeds[0,h]=S.Rational(h,3);seeds[2,h]=S.Rational(-1,h+1)
  c=stencil_residues(r,seeds);mats=harmonic_matrices(r,S.Rational(2,3),c)
  yes(rank_one_type(mats)[0]=='corner','critical_pencil_classification')
  for q,C in enumerate(mats,1):
   target=S.zeros(r);target[-1,-1]=sum(v for (j,h),v in seeds.items() if h==q)
   eq(C,target,'higher_pole_corner_coefficients')
   P=sum(v*z**j for (j,h),v in c.items() if h==q)
   Q=sum(v*z**j for (j,h),v in seeds.items() if h==q)
   eq(P,(z-1)**d*Q/S.factorial(d),'finite_difference_residue_inversion')
  # One more difference produces zero harmonic pencil.
  c1={}
  for (j,h),v in c.items():
   c1[j,h]=c1.get((j,h),0)-v;c1[j+1,h]=c1.get((j+1,h),0)+v
  yes(rank_one_type(harmonic_matrices(r,S.Rational(2,3),c1))[0]=='zero','zero_pencil')
  # A repeated-pole perturbation preserving critical decay but losing rank one.
  # For q>d+1 its perturbation does not change the x^(-d-1) leading term.
  bad=dict(c);bad[0,d+2]=bad.get((0,d+2),0)+1
  yes(rank_one_type(harmonic_matrices(r,S.Rational(2,3),bad))[0]=='not_rank_one',
      'deliberate_perturbation_rejected')

# The geometric branch at faster decay: not a Delta^2 stencil.
c={(0,2):S.Integer(1),(0,1):S.Rational(-3,2),(1,1):S.Integer(2),(2,1):S.Rational(-1,2)}
R=sum(v/(x+1+j)**h for (j,h),v in c.items())
eq(R,2/((x+1)**2*(x+2)*(x+3)),'faster_decay_counterexample')
Cs=harmonic_matrices(2,S.Integer(1),c)
eq(Cs[0],S.zeros(2),'faster_decay_counterexample')
eq(Cs[1],S.Matrix([[1,-1],[-1,1]]),'faster_decay_counterexample')
yes(rank_one_type(Cs)==('geometric',-1),'faster_decay_counterexample')
yes(S.rem(S.Integer(1),(z-1)**2,z)==1,'faster_decay_counterexample')

# Explicit finite cutoff and the Li_{2,2} generator, coefficient by coefficient.
M=S.symbols('M',integer=True,positive=True);h=S.symbols('h')
P=-S.Rational(7,16)-S.Rational(3,4)/(M+2)+S.Rational(7,4)/(M+2)**2+S.Rational(7,8)/(M+1)**2-S.Rational(1,2)/(M+1)**4
Q=S.Rational(3,8)-S.Rational(1,2)/(M+1)**2+S.Rational(1,2)/(M+2)**2
for n in range(1,13):
 h2=sum(S.Rational(1,k*k) for k in range(1,n+1))
 direct=partition_direct(2,n-1,S.Integer(1),S.Integer(2))
 eq(direct,(P+Q*h).subs({M:n,h:h2}),'explicit_cutoff_formula')
# The shifts z^-2 require two more Taylor coefficients than the requested range.
L=44
Li=lambda p:sum(z**n/S.Integer(n)**p for n in range(1,L+3))
Li22=sum(z**n*sum(S.Rational(1,k*k) for k in range(1,n))/n**2 for n in range(1,L+3))
F=(1-z)/(2*z**2)*Li22+(10-7*z)/(8*z**2*(1-z))*Li(2)+(4*z-7)/(4*z**2)*Li(1)-Li(4)/(2*z)+1/(2*z)-S.Rational(7,16)/(1-z)
# Avoid slow high-order symbolic series of one expanded rational expression.
poly=S.Poly(S.cancel((1-z)*F*z**2),z)
coef=lambda k: poly.coeff_monomial(z**k)
for n in range(0,L):
 actual=sum(coef(k) for k in range(n+3)) # coefficient z^(n+2) after /(1-z)
 if n==0: expected=0
 else: expected=(P+Q*h).subs({M:n,h:sum(S.Rational(1,k*k) for k in range(1,n+1))})
 eq(actual,expected,'polylog_generator_coefficients')
eq(coef(0),0,'removable_generator_singularity');eq(coef(1),0,'removable_generator_singularity')

# Stieltjes coefficient rule, including the pole-times-next-coefficient term.
u=S.symbols('u');K=6
bs=S.symbols('b1:'+str(K+3));gs=S.symbols('g0:'+str(K+1));us=S.symbols('U0:'+str(K+1))
B=sum(bs[j-1]*u**j/S.factorial(j) for j in range(1,K+2))
ZG=1/u+sum((-1)**m*gs[m]*u**m/S.factorial(m) for m in range(K+1))
UG=sum(us[k]*u**k/S.factorial(k) for k in range(K+1))
for k in range(K+1):
 target=us[k]+bs[k]/(k+1)+sum(S.binomial(k,j)*bs[j-1]*(-1)**(k-j)*gs[k-j] for j in range(1,k+1))
 eq(S.expand(UG+B*ZG).coeff(u,k)*S.factorial(k),target,'all_jet_coefficient_rule')
for d in (2,4,6,8,10):
 c=S.prod(1+u/S.Integer(j) for j in range(1,d+1))
 for k in range(0,7):
  xs=[(-1)**(q-1)*S.factorial(q-1)*sum(S.Rational(1,j**q) for j in range(1,d+1)) for q in range(1,k+1)]
  eq(S.expand(c).coeff(u,k)*S.factorial(k),complete_bell(xs),'harmonic_residue_bell')

out={'status':'passed','arithmetic':'exact SymPy rational/symbolic arithmetic',
     'assertions':sum(counts.values()),'by_family':dict(counts),
     'examples':examples,'elapsed_seconds':round(time.time()-start,3),
     'scope':'Finite regression checks; the all-order results are proved in the article.'}
(ROOT/'results').mkdir(exist_ok=True)
(ROOT/'results/exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='examples'},indent=2))
