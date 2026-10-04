#!/usr/bin/env python3
"""Literal current84-to83 transfer of the historical empty multiplicative-gamma chart."""
import argparse,hashlib,json,math,random
from fractions import Fraction
from pathlib import Path
PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'review_complete74_asymmetric_scale_math.md':'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
 'complete75_multiplicative_gamma86_obstruction.py':'58078beb773b23f311292feba17651dbb87bc42d2fa70b0cfd8354baa68276f9',
 'complete75_multiplicative_gamma86_obstruction.json':'58dbeee464988bb02a532df6b237d4544415d9451fd440f64c33ef1424939710',
 'complete75_multiplicative_gamma86_obstruction.md':'1800d2c85b5fe895f348d7bdf9fcaf0a8860f93b2d3625a399c587d3e7982986',
}
def check(ok,msg):
 if not ok:raise ValueError(msg)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,sign=1):
 c=a.copy()+[0]*max(0,len(b)-len(a))
 for i,v in enumerate(b):c[i]+=sign*v
 return trim(c)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def ev(a,z):
 v=0
 for c in reversed(a):v=v*z+c
 return v
def divide(a,b):
 check(b[-1]==1,'monic division');r=a.copy();q=[0]*max(1,len(a)-len(b)+1)
 while r!=[0] and len(r)>=len(b):
  j=len(r)-len(b);v=r[-1];q[j]+=v
  for i,c in enumerate(b):r[i+j]-=v*c
  trim(r)
 return trim(q),r
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def huge_digest(n):return hashlib.sha256(hex(n).encode()).hexdigest()
def run(source,values):
 e=values.copy()
 for name,op,l,r in source:
  a=e[l] if isinstance(l,str) else l;b=e[r] if isinstance(r,str) else r
  e[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
def make(root):
 for name,pin in PINS.items():check(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'pin '+name)
 parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet'];old=parent['source']
 check(['gamma_sum','+','rho','sigma'] in old,'deleted gate')
 check([r for r in old if 'gamma_sum' in r[2:]]==[['gam','*','gamma_sum','a4m5']],'private gamma')
 source=[]
 for row in old:
  if row[0] in ['gamma_sum','modulus_multiple']:continue
  if row[0]=='gam':
   source.extend([['modulus_multiple','*','rho','a4m5'],['gam','*','sigma','modulus_multiple']])
  else:source.append(row.copy())
 check(len(source)==83,'83 source');known=set(parent['free']);degrees={v:0 if v in parent['fixed_numerals'] else 1 for v in parent['free']}
 for name,op,l,r in source:
  check(name not in known and all(not isinstance(v,str) or v in known for v in [l,r]),'closure')
  dl=degrees[l] if isinstance(l,str) else 0;dr=degrees[r] if isinstance(r,str) else 0
  degrees[name]=dl+dr if op=='*' else max(dl,dr);known.add(name)
 live={parent['output']}
 for name,op,l,r in reversed(source):
  check(name in live,'dead gate '+name)
  live.update(v for v in [l,r] if isinstance(v,str))
 check(set(parent['free'])<=live,'free liveness')
 M=sum(row[1]=='*' for row in source);check((M,len(source)-M)==(47,36),'ledger')
 # Exact private-block coefficient identity in rho,sigma,H.
 # rho + rho*(sigma-1) = rho*sigma; multiply the resulting monomial by H.
 left={(1,0,0):1}
 for exp,c in [((1,1,0),1),((1,0,0),-1)]:left[exp]=left.get(exp,0)+c
 left={e:c for e,c in left.items() if c};check(left=={(1,1,0):1},'private polynomial identity')
 check([r for r in source if r[0]!='gam' and r[0]!='modulus_multiple']==[r for r in old if r[0] not in ['gam','modulus_multiple','gamma_sum']],'all retained definitions')
 rng=random.Random(830047);counts={'signed':0,'rational':0,'sigma_one':0,'retained_equalities':0}
 for trial in range(48):
  values={v:rng.randrange(-3,5) for v in parent['free']}
  if trial<16:
   values={v:Fraction(n,rng.randrange(1,5)) for v,n in values.items()};kind='rational'
  elif trial<32:values['sigma']=1;kind='sigma_one'
  else:kind='signed'
  prior=values.copy();prior['sigma']=values['rho']*(values['sigma']-1)
  x=run(source,values);y=run(old,prior)
  for name,_,_,_ in source:check(x[name]==y[name],'retained register '+name);counts['retained_equalities']+=1
  counts[kind]+=1
 factors=parent['factors'];wanted=[22,19,32,60,7,2,46]
 dense=[]
 for prime,beta,ell in [(1000000007,15,10),(1000000009,31,50)]:
  constants={'Bm1':beta,'Kconstant':7,'twice_cell_bits':ell,'inner_bits':5,'MC':6,'MF':19}
  e={v:[constants[v]] if v in constants else [0,1] for v in parent['free']}
  for name,op,l,r in source:
   a=e[l] if isinstance(l,str) else [l];b=e[r] if isinstance(r,str) else [r]
   c=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
   e[name]=trim([v%prime for v in c])
  actual=[len(e[f])-1 for f in factors];check(actual==wanted,'factor degrees')
  poly=e[parent['output']];check(len(poly)-1==188,'dense degree')
  lead=-(1<<18)*(ell+3)*pow(beta,111,prime)%prime
  check(poly[-1]==lead,'diagonal uniform leader')
  dense.append({'prime':prime,'fixed_diagnostic_constants':constants,'factor_degrees':actual,'degree':188,'leading_coefficient':poly[-1],'coefficients_sha256':digest(poly)})
 # Monic projection polynomials, independently compared with explicit Chebyshev coefficients.
 G=[[0],[0],[1]]
 for n in range(2,63):G.append(add(add([0]+G[n],G[n-1],-1),[2**(n-1)]))
 def psi(n):
  if n==0:return [0]
  p=[0]*n
  for j in range((n-1)//2+1):p[n-1-2*j]=(-1)**j*math.comb(n-1-j,j)
  return trim(p)
 for n in range(1,64):
  E=add([2*x for x in psi(n)],psi(n-1),-1)
  check(add(mul([-5,2],G[n]),[2**n])==E,'independent projection identity')
  if n>=2:check(len(G[n])-1==n-2 and G[n][-1]==1 and sum(map(abs,G[n]))<=2**n,'coefficient bound')
 remainders=[]
 for u in range(3,18,2):
  for R in range(u+2,42,2):
   Q,r=divide(G[R],G[u]);check(r!=[0] and add(mul(Q,G[u]),r)==G[R],'exact nonzero remainder')
   L=2**u;B=L+2;bound=B**(R-2);check(sum(map(abs,r))<=bound,'remainder coefficient bound')
   Z=L+bound+1;gu=ev(G[u],Z);gr=ev(G[R],Z);rv=ev(r,Z)
   check(rv!=0 and abs(rv)<gu and gr%gu!=0,'large evaluation nondivisibility')
   remainders.append({'u':u,'R':R,'remainder_sha256':digest(r),'remainder_l1_bits':sum(map(abs,r)).bit_length(),'large_Z_bits':Z.bit_length(),'evaluation_remainder_sha256':huge_digest(rv)})
 native=[]
 for R in [7,11,15,19,23,27]:
  r=(R-1)//2;X=2**R;twoy=sum(math.comb(2*r,r+j)*X**j for j in range(r+1));check(twoy%2==0,'integer Y')
  Z=twoy*(X+1)+4
  for u in [3,5]:
   if 2*u>=R:continue
   L=2**u;B=L+2;check(Z>2**(R*(R+1)//2)>L+B**(R-2),'native dominance bound')
   gu,gr=ev(G[u],Z),ev(G[R],Z);check(gu>0 and gr%gu!=0,'native numerical projection')
   native.append({'u':u,'R':R,'Z_bits':Z.bit_length(),'rho_bits':gu.bit_length(),'gamma_bits':gr.bit_length(),'nonzero_remainder_sha256':huge_digest(gr%gu)})
 packet={'source':source,'output':parent['output'],'free':parent['free'],'witnesses':parent['witnesses'],'witness_domain':parent['witness_domain'],'ordinary_input':parent['ordinary_input'],'fixed_numerals':parent['fixed_numerals'],'factors':factors,
         'ledger':{'multiplications':47,'additions_subtractions':36,'total':83,'witnesses':18},'exact_degree':188,'factor_exact_degrees':wanted,'gate_upper_degree':degrees[parent['output']],
         'coordinate_change':'sigma_parent=rho*(sigma_candidate-1); gamma=rho*sigma_candidate',
         'all_ring_identity':'P83(sigma)=P84(sigma_parent=rho*(sigma-1))','positive_zero_status':'EMPTY on every inherited valid fixed compiler slice; historical phenomenon transferred to current source',
         'scope':'Full current source, not a universal representation or a relaxation with a completeness theorem.'}
 return {'schema':'current83-multiplicative-gamma-empty-v1','pins':PINS,'packet':packet,'source_sha256':digest(source),
         'all_value_checks':counts,'degree':{'uniform_leader':'32*Q^111*h*rho*sigma*delta^2*i^4*(eta+zeta)^13*w^18*s^31*Nt_top*T^2*f^2','diagonal_coefficient':'-2^18*(twice_cell_bits+3)*Bm1^111','diagnostics':dense},
         'polynomial_checks':{'projection_identities':63,'monic_coefficient_bounds':62,'remainders':remainders,'native_formula_evaluations':native},
         'historical_provenance':'The empty multiplicative-gamma shortcut is already proved in complete75_multiplicative_gamma86_obstruction; this emits its actual84-to83 successor and a monic remainder proof.',
         'full_positive_compiler_zeros_materialized':False}
def equal(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=make(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:check(equal(r,json.loads(a.expect.read_text())),'receipt mismatch')
 print('PASS: literal83=47M36A; degree188; inherited empty-chart proof, no universal bound')
if __name__=='__main__':main()
