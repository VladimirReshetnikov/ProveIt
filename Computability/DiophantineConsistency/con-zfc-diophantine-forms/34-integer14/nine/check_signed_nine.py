"""Fresh finite algebra checks. These do not replace the universal proof."""
from pathlib import Path
from itertools import combinations_with_replacement,product
from math import isqrt
import json,random
from circuit_support import evaluate,audit_body
from check_degree import rewrite
HERE=Path(__file__).resolve().parent

def fixed_values(co,ports,z,y,p):
 ans={'z_index':z,'y_index':y}
 for row in co['coefficient_records']:
  ans[row['name']]=sum(t['coefficient']*prodmod([pow(a,e,p) for a,e in zip(ports,t['powers'])],p) for t in row['coefficient_polynomial_in_fixed_ports'])%p
 return ans

def prodmod(xs,p):
 z=1
 for x in xs:z=z*x%p
 return z

def direct_digit(co,B,fixed,p):
 if B%p==0:return 0
 nu=co['nu'];L=co['L'];five=[5**j for j in range(nu+1)];s=0
 # Choose exactly four symbols, including the slack symbol -1.
 for inds in combinations_with_replacement(range(-1,nu+1),4):
  expo=sum(five[j] for j in inds if j>=0)
  s=(s+pow(B,(L-expo)%(p-1),p))%p
 s=s*fixed['z_index']
 for row in co['coefficient_records']:s+=fixed[row['name']]*pow(B,(L-row['expo'])%(p-1),p)
 return s%p

def main():
 co=json.loads((HERE/'INDEX_CONSTANTS.json').read_text());base=json.loads((HERE/'base31.json').read_text());b=json.loads((HERE/'nine31_signed_quadratic.json').read_text());pos=json.loads((HERE/'nine31_signed_quadratic_positive.json').read_text());rng=random.Random(202610230250)
 count=digits=0
 for p in (101,1009,65537):
  for trial in range(12):
   fixed=fixed_values(co,[rng.randrange(p) for _ in range(4)],rng.randrange(p),rng.randrange(p),p)
   v={k:rng.randrange(p) for k in base['variables']}
   old=evaluate(base,fixed,v,p);new=evaluate(b,fixed,v,p)
   ns={k:new[i] for k,i in b['named_nodes'].items()}
   for k in ['b','B','q','ell','lambda','e','R','P','K','A','C','D','E','F','Gp','H','I','a0','a1','margin']:
    assert old[base['named_nodes'][k]]==ns[k],(p,trial,k)
    count+=1
   alt=rewrite(ns,v['n'])
   assert alt['V1square_minus_a1']%p==(ns['V1']**2-ns['a1'])%p
   assert alt['inner']%p==ns['inner']
   assert alt['output']%p==new[b['output']]
   assert alt['deltaD']%p==(ns['M_D']**2-ns['D'])%p
   assert alt['deltaF']%p==(ns['M_F']**2-ns['F'])%p
   assert alt['deltaI']%p==(ns['M_I']**2-ns['I'])%p
   count+=6
   pv={dst:v[src]+1 for src,dst in zip(['epsilon','g0','h0','s0','w0','phi','i0','j0','n'],['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus'])}
   assert evaluate(pos,fixed,pv,p)[pos['output']]==new[b['output']];count+=1
   if trial==0 and ns['B']:
    assert direct_digit(co,ns['B'],fixed,p)==ns['e'];digits+=1
 # Every coefficient alias is checked as an exact sparse polynomial/literal identity.
 records={r['name']:r['coefficient_polynomial_in_fixed_ports'] for r in co['coefficient_records']}
 for name,alias in b['coefficient_aliases'].items():
  expected=[{'powers':[0,0,0,0],'coefficient':alias['literal']}] if 'literal' in alias else records[alias['fixed']]
  assert records[name]==expected
 majors=0;edge={'negative_R':0,'C_zero':0,'H_zero':0}
 for R,U,Y,bv,w,phi,i,j,h in product(list(range(-8,0))+list(range(1,9)),[1,2],[1,2],[2,3],[1,2],[0,1,2],[1,2],[1,2],[1,2]):
  r=bv*w+phi;sig=Y*(U+1);A=R*sig;C=2*R+1+r;H=2*R+1+j*C
  J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A);I=(G*G-1)*H*H+1
  md=sig*(R*C+r*r);mf=A*E+1;tc=C*H+r*r;mi=F*(D*tc+2*H*H+A*A)-A*A+1
  P=2*(R*Y)**2*U;K=R+1+h*(P-1);a0=(P*P-1)*K*K+1;v0=P*K+1;v1=md*mf*mi+1
  assert md>=1 and md*md>=D and mf>=1 and mf*mf>=F and mi>=1 and mi*mi>=abs(I)
  assert tc>=abs(C*H) and R*C+r*r>abs(R*C)
  assert v0>=2 and v1>=2 and (v0-1)**2>=abs(a0) and (v1-1)**2>=abs(D*F*I)
  majors+=1
  edge['negative_R']+=R<0;edge['C_zero']+=C==0;edge['H_zero']+=H==0
 def sq(a):return a>=0 and isqrt(a)**2==a
 def final(a,b,u,v,m,M,V0,V1,n):
  om=u*m;th=u*(n+M)+v-om*(2*M+V0*V1)
  return (th*th-om*om*(a+V0*V0*b))**2-4*om**4*V0*V0*a*b
 sound=complete=0
 for a0,a1,u,v,m in product(range(-3,5),range(-3,5),[-3,-2,-1,1,2,3],range(-3,4),range(-1,3)):
  V0=isqrt(abs(a0))+2;V1=isqrt(abs(a1))+2;M=abs(v)+1;rhs=sq(a0) and sq(a1) and v%u==0 and m>0
  for n in range(8):
   assert final(a0,a1,u,v,m,M,V0,V1,n)!=0 or rhs;sound+=1
  if rhs:
   Z=2*M+V0*V1+isqrt(a0)+V0*isqrt(a1);n=m*Z-M-v//u
   assert n>=0 and final(a0,a1,u,v,m,M,V0,V1,n)==0;complete+=1
 result={'status':'PASS','circuit':audit_body(b),'positive_circuit':audit_body(pos),'named_algebra_comparisons':count,'explicit_digit_sum_checks':digits,'exact_alias_checks':len(records),'structured_bound_assignments':majors,'edge_cases':edge,'signed_finalizer_soundness_assignments':sound,'explicit_completeness_witnesses':complete}
 (HERE/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
