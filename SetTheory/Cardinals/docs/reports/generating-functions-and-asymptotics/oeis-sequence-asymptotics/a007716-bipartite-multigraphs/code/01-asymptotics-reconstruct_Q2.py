#!/usr/bin/env python3
"""Independent Q2 reconstruction from a compressed seven-term decomposition.
No imports of any producer implementation. Bell shifts are obtained by
implicitly expanding W(n-s), rather than using the producer's shift formulas.
"""
from pathlib import Path
import json
import sympy as S
from sympy.functions.combinatorial.numbers import stirling
w,s,t,m,e=S.symbols('w s t m e',positive=True)

# Solve (1+delta/w)*exp(delta)=1-s/n successively to degree 3.
u1,u2,u3=S.symbols('u1 u2 u3')
delta=u1*e+u2*e**2+u3*e**3
implicit=S.expand((1+delta/w)*(1+delta+delta**2/2+delta**3/6))
sol={}
for degree,u in enumerate([u1,u2,u3],1):
 rhs=-s if degree==1 else 0
 sol[u]=S.factor(S.solve(S.Eq(implicit.coeff(e,degree).subs(sol),rhs),u)[0])
delta=S.expand(delta.subs(sol))

def trunc(poly,k):
 return S.Add(*(S.expand(poly).coeff(e,j)*e**j for j in range(k+1)))

# Explicit first Bell correction, derived independently in the earlier audit.
beta=-w*w*(2*w*w+7*w+10)/(24*(1+w)**3)
f=w-1+1/w
fshift=f+sum(S.diff(f,w,j)*trunc(delta**j,3)/S.factorial(j) for j in range(1,4))
logamp=-(delta/(1+w)-delta**2/(2*(1+w)**2))/2
betashift=(beta+S.diff(beta,w)*delta)*e*(1+s*e)
logratio=trunc((fshift-f)/e-s*fshift+logamp+betashift-beta*e,2)
coeff=[S.factor(S.expand(logratio).coeff(e,j)) for j in range(3)]
if S.cancel(coeff[0]+s*w)!=0:raise RuntimeError('Leading Bell shift failed')
p1,p2=coeff[1:]

def correction(moved,left,right,degree):
 log1=p1.subs(s,left)+p1.subs(s,right)-moved*(moved-1)/2
 if degree==1:return log1
 log2=p2.subs(s,left)+p2.subs(s,right)-moved*(moved-1)*(2*moved-1)/12
 return log2+log1**2/2

def poisson(poly):
 out=0
 for (power,),c in S.Poly(S.expand(poly),t).terms():
  touchard=sum(stirling(power,j,kind=2)*(w*w/2)**j for j in range(power+1))
  out+=c*touchard
 return S.factor(out)

# For t disjoint transpositions, E(one selected)=1 and E(two)=1+2=3.
# Squaring the marked partition count gives t^2+6*binom(t,2),
# including the same transposition selected on both shores.
# A single 3-cycle has singleton marked weight 1, yielding 2*(t+1).
components={
 'pure_transpositions_no_marks':correction(2*t,t,t,2),
 'pure_transpositions_one_mark':2*w*t*correction(2*t,t,t+1,1),
 'pure_transpositions_two_marks':w*w*(4*t*t-3*t),
 'one_3_cycle_no_marks':w**4/S.Integer(3)*correction(2*t+3,t+2,t+2,1),
 'one_3_cycle_one_mark':2*w**5/S.Integer(3)*(t+1),
 'two_3_cycles_no_marks':w**8/S.Integer(18),
 'one_4_cycle_no_marks':w**6/S.Integer(4),
}
averaged={name:poisson(expr) for name,expr in components.items()}
Q2=S.factor(sum(averaged.values()))
Q1=poisson(correction(2*t,t,t,1)+2*w*t+w**4/3)
expected1=w*w*(w**4+11*w**3+22*w*w+12*w-6)/(12*(w+1)**2)
expected2=w**3*(w**10+23*w**9+343*w**8+1441*w**7+2600*w**6+2440*w**5+1944*w**4+1980*w**3+1068*w*w-324*w-576)/(288*(w+1)**5)
if S.cancel(Q1-expected1)!=0:raise RuntimeError('Q1 mismatch')
if S.cancel(Q2-expected2)!=0:raise RuntimeError('Q2 mismatch')
if any(q.has(S.Float) for q in [Q1,Q2,*coeff]):raise RuntimeError('Floating arithmetic entered')
out={'status':'PASS','method':'Implicit Lambert-W shift; seven compressed cycle/mark contributions; Poisson moments by Stirling numbers of the second kind','W_shift_coefficients':{str(u):str(v) for u,v in sol.items()},'Bell_log_shift':[str(v) for v in coeff],'Q1':str(Q1),'Q2':str(Q2),'Q2_components':{k:str(v) for k,v in averaged.items()},'scope':'Exact symbolic coefficient reconstruction. Analytic remainder proofs are in article.tex; this output checks exact coefficients only.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
