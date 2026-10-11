"""Independent exact matrix and Bell-generator audit of the formal IBP theorem.
No delivered reduction program is imported. Infinite statements rest on proofs.
"""
from pathlib import Path
from functools import lru_cache
import json,time
import sympy as S
V=Path(__file__).resolve().parent
u=S.symbols('u0:14');t=S.Symbol('t');gamma=S.Symbol('gamma');z={j:S.Symbol('z'+str(j)) for j in range(2,15)}
def D(p):return S.expand(sum(u[j+1]*S.diff(p,u[j]) for j in range(13)))
@lru_cache(None)
def partitions(n,m=None):
 if not n:return ((),)
 if m is None:m=n
 return tuple((a,)+p for a in range(min(n,m),0,-1) for p in partitions(n-a,a))
def mon(p):return S.prod(u[a-1] for a in p)
def normal(p):return len(p)>1 and p[0]==p[1]
def vector(poly,parts):
 d=S.Poly(poly,*u).as_dict();return S.Matrix([d.get(tuple(p.count(j+1) for j in range(len(u))),0) for p in parts])
records=[];matrices={};start=time.time()
for w in range(2,15):
 parts=partitions(w);prev=partitions(w-1);basis=tuple(p for p in parts if normal(p));cols=[vector(D(mon(p)),parts) for p in prev]+[vector(mon(p),parts) for p in basis];M=S.Matrix.hstack(*cols);assert M.rows==M.cols==len(parts);inverse=M.inv();assert M*inverse==inverse*M==S.eye(len(parts));matrices[w]=(parts,prev,basis,inverse)
 factor_checks=[]
 for i,p in enumerate(parts):
  coeff=inverse[:,i];assert all(not c or len(q)==len(p) for c,q in zip(coeff,prev+basis));factor_checks.append(True)
 records.append(dict(weight=w,ambient_dimension=len(parts),derivative_dimension=len(prev),normal_dimension=len(basis),both_inverse_certificates=True,factor_degree_preserved=all(factor_checks)));print('weight',w,'exact matrix',len(parts),flush=True)
def decompose(poly,w):
 parts,prev,basis,inverse=matrices[w];c=inverse*vector(poly,parts);Q=S.expand(sum(a*mon(p) for a,p in zip(c[:len(prev)],prev)));N=S.expand(sum(a*mon(p) for a,p in zip(c[len(prev):],basis)));assert S.expand(D(Q)+N-poly)==0;return Q,N
A=[S.Integer(1),u[0]];pairs={0:(S.Integer(0),S.Integer(1)),1:(S.Integer(0),u[0])};parity=[];bell=[];concomitants=[]
for m in range(2,13):
 A.append(S.expand(u[0]*A[-1]-D(A[-1])));Q,N=decompose(A[m],m);pairs[m]=(Q,N)
 assert all(sum(e)%2==m%2 for e,c in S.Poly(N,*u).terms());parity.append(True);print("inverse Gamma degree",m,flush=True)
 direct=S.expand(S.factorial(m)*sum(S.prod((((-1)**(j+1)*u[j-1]/S.factorial(j))**p.count(j))/S.factorial(p.count(j)) for j in set(p)) for p in partitions(m)));assert S.expand(direct-A[m])==0;bell.append(True)
 # Formal Lagrange concomitant, independent of the matrix projection.
 B=lambda j:S.expand((-1)**j*A[j].subs({q:-q for q in u},simultaneous=True))
 L=S.expand(sum((-1)**j*B(j)*B(m-1-j).subs({q:-q for q in u},simultaneous=True) for j in range(m)))
 assert S.expand(D(L)-((-1)**m*A[m]-A[m].subs({q:-q for q in u},simultaneous=True)))==0;concomitants.append(True)
pair_checks=0
for m in range(1,12):
 Q,N=pairs[m];Snext,Rnext=decompose(u[0]*N-u[1]*Q,m+1);qnext,nnext=pairs[m+1];assert S.expand(Rnext-nnext)==0 and S.expand(Snext+u[0]*Q-N-D(Q)-qnext)==0;pair_checks+=1
printed={4:u[0]**4-u[1]**2,5:u[0]**5-5*u[0]*u[1]**2,6:u[0]**6-15*u[0]**2*u[1]**2+u[2]**2,7:u[0]**7-35*u[0]**3*u[1]**2+7*u[0]*u[2]**2,8:u[0]**8-70*u[0]**4*u[1]**2+28*u[0]**2*u[2]**2-7*u[1]**4-u[3]**2}
assert all(S.expand(pairs[m][1]-p)==0 for m,p in printed.items())
# Endpoint constants from exact Laurent multiplication, including cross-poles.
x=S.Symbol('x');local=-1/x-gamma+sum((-1)**j*z[j]*x**(j-1) for j in range(2,13));rules={u[j]:S.diff(local,x,j) for j in range(6)};end={u[0]:-gamma}|{u[j]:(-1)**(j+1)*S.factorial(j)*z[j+1] for j in range(1,6)}
def E(p):
 expr=S.expand(p.subs(rules,simultaneous=True));ct=expr.coeff(x,0);return S.expand(p.subs(end,simultaneous=True)-ct)
assert E(u[0]*u[1])==-z[3];assert E(u[1]*u[2])==4*z[5];assert E(u[0]**2)==2*z[2]
# A naive multiplicative constant extraction gives a false endpoint.
wrong=S.expand((u[0]*u[1]).subs(end,simultaneous=True)-(-gamma)*z[2]);assert wrong==0 and E(u[0]*u[1])!=wrong
out=dict(status='PASS',matrix_weights=[2,14],matrices=records,monomial_decompositions_checked=sum(r['ambient_dimension'] for r in records),inverse_gamma_degrees=[2,12],factor_parity_checks=len(parity),independent_Bell_generator_checks=len(bell),independent_Lagrange_concomitant_checks=len(concomitants),pair_recurrence_checks=pair_checks,printed_normal_forms_checked=len(printed),endpoint_checks=3,missing_cross_pole_control_detected=True,normal_forms={str(m):str(p) for m,p in printed.items()},elapsed_seconds=round(time.time()-start,3),scope='Exact finite two-sided matrix certificates, independent exponential Bell construction and polynomial Lagrange identity; formal normal forms and finite endpoints, not arithmetic independence or all-weight proof-assistant verification.')
(V/'ibp-normal-forms-exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('PASS',out['monomial_decompositions_checked'],'decompositions')
