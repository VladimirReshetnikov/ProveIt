"""Exact order-ten exceptional case; run on a copy to preserve evidence.
The native companion independently verifies every coefficient.
"""
"""Exact retained determinant at the only unresolved order-ten residue below B5."""
from pathlib import Path
import json,hashlib,sys,time
import sympy as s
from sympy.functions.combinatorial.numbers import stirling
sys.set_int_max_str_digits(200000)
V=Path(__file__).resolve().parent;a=5;b=962;started=time.monotonic()
y=s.symbols('y');U={j:2*s.bernoulli(2*b-2*j) for j in range(1,2*a)}
def falling(v,k):return s.prod(v-r for r in range(k))
rows=[];other=[];newton=[]
for i in range(a):
 n=b-a+i;poly=s.Poly((2*n+2-y)*falling(4*n+2-y,2*i),y)
 d=[sum(poly.nth(k)*stirling(k,h,kind=2) for k in range(h,2*i+2)) for h in range(2*i+2)]
 dd=[sum((-1)**(h-r)*s.binomial(h,r)*poly.eval(r) for r in range(h+1))/s.factorial(h) for h in range(2*i+2)]
 assert d==dd and all(v.q==1 for v in d)
 newton.append([str(v) for v in d]);row=[];alt=[]
 for ell in range(a):
  N=2*(n-ell)+1;R=2*b-2*a+2+2*ell;gap=R-N
  ratio=s.prod(N+r for r in range(1,gap+1)) if gap>=0 else s.S.One/s.prod(R+r for r in range(1,-gap+1))
  assert ratio==s.factorial(R)/s.factorial(N)
  F=falling(2*n,2*ell)*s.prod(2*n+3+r for r in range(2*ell))/s.factorial(2*ell+1)
  correction=sum(d[2*k+1]*falling(N,2*k+1)*U[a-i+ell+k] for k in range(i+1))
  value=s.cancel(2*F+ratio*correction/((2*n+1)*(2*n+2)*s.factorial(2*ell+2)))
  correction2=sum(dd[2*k+1]*s.factorial(N)/s.factorial(N-2*k-1)*U[a-i+ell+k] for k in range(i+1))
  value2=s.cancel(2*F+s.factorial(R)/s.factorial(N)*correction2/((2*n+1)*(2*n+2)*s.factorial(2*ell+2)))
  assert value==value2;row.append(value);alt.append(value2)
 rows.append(row);other.append(alt);print('Exact retained row',i,flush=True)
A=s.Matrix(rows);det=A.det(method='domain-ge');assert det!=0
inverse=A.inv(method='DM');assert A*inverse==inverse*A==s.eye(a)
payload=dict(status='PASS',a=a,b=b,tail_orders=[2*a,2*b],retained_dimension=a,bernoulli_coordinates={str(j):str(v) for j,v in U.items()},newton_coefficients=newton,matrix=[[str(c) for c in row] for row in rows],inverse=[[str(inverse[i,j]) for j in range(a)] for i in range(a)],determinant=str(det),two_exact_entry_constructions_agree=True,both_inverse_products=True,determinant_nonzero=True,determinant_numerator_decimal_digits=len(str(abs(s.numer(det)))),determinant_denominator_decimal_digits=len(str(s.denom(det))),elapsed_seconds=round(time.monotonic()-started,3),scope='Exact five-square retained matrix at a=5,b=962 from the quartic source normalization, constructed using independent Stirling and finite-difference Newton coefficients. This finite exceptional case must be combined with audited infinite congruence and eventual-rank proofs before claiming the full order-ten family. No arithmetic independence or Gaussian period statement.')
out=V/'order-ten-exception-probe.json';out.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
print('Exact exception determinant nonzero; both inverse products PASS; numerator digits',payload['determinant_numerator_decimal_digits'],flush=True)
