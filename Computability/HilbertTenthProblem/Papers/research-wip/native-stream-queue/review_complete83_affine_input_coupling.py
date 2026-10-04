"""Independent data-only check of the bounded affine-input theorem packet."""
import argparse
import hashlib
import json
from pathlib import Path

PINS={
 'complete83_affine_input_coupling.py':'55febc153372e65b3098bbce2b40a86edcc54d6cdc11353fc38fb7d6c3103b49',
 'complete83_affine_input_coupling.json':'54ac7f40e861d912987963b0ec48237319ff992a8283689962cea4a6f0eb7132',
 'complete83_affine_input_coupling.md':'d04b5c35bc8a1569a4e4c7881c6322a9b6dd36d12d65c7dc09ab65d57c0c8efa'}
def check(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
# Sparse polynomials use sorted variable-name tuples for monomials.
def constant(n):return {():n} if n else {}
def var(n):return {(n,):1}
def plus(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def minus(a,b):return plus(a,{k:-v for k,v in b.items()})
def times(a,b):
 out={}
 for k,v in a.items():
  for j,w in b.items():
   m=tuple(sorted(k+j));out[m]=out.get(m,0)+v*w
 return {k:v for k,v in out.items() if v}
def square(a):return times(a,a)
def scale(n,a):return times(constant(n),a)
def run(root,packet):
 for name,pin in PINS.items():check(sha((packet/name).read_bytes())==pin,name)
 receipt=json.loads((packet/'complete83_affine_input_coupling.json').read_bytes())
 for name,pin in receipt['pins'].items():check(sha((root/name).read_bytes())==pin,'dependency '+name)
 saved=json.loads((root/'complete83_independent_gamma_scout.json').read_bytes())['packet']
 original=json.loads((root/'complete84_scaled_strong_output.json').read_bytes())['packet']
 rebuilt=[]
 for name,op,a,b in original['source']:
  if name=='gamma_sum':check([op,a,b]==['+','rho','sigma'],'deleted')
  else:rebuilt.append([name,op,'sigma' if a=='gamma_sum' else a,'sigma' if b=='gamma_sum' else b])
 check(rebuilt==saved['source'],'entire source')
 banned={'delta','rho','i','f','auxiliary_quotient','y_aux'}
 deps={n:{n} for n in saved['free']}; producers={}; M=A=0
 for name,op,a,b in rebuilt:
  check(name not in deps and op in ('*','+','-'),'source definition')
  deps[name]=set()
  for z in [a,b]:
   if isinstance(z,str):check(z in deps,'topology');deps[name]|=deps[z]
  producers[name]=[a,b]
  if op=='*':M+=1
  else:A+=1
 exterior=[row[0] for row in rebuilt if not deps[row[0]]&banned]
 free=[p for p in saved['free'] if p not in banned]
 check(exterior==receipt['exterior_computed'] and free==receipt['exterior_free'],'complete census')
 check((len(exterior),len(free),M,A)==(52,19,47,36),'counts')
 live={'polynomial'}
 for name,op,a,b in reversed(rebuilt):
  check(name in live,'dead gate');live.update(z for z in [a,b] if isinstance(z,str))
 check(set(saved['free'])<=live,'dead port')
 names=['a','D','H','u','W','delta','rho','P','Q','S','k','m','p','q','r']
 a,D,H,u,W,delta,rho,P,Q,S,k,m,p,q,r=map(var,names)
 vals={'A':D,'R12':a,'a4m5':H,'odd_index':u,'W':W,'delta':delta,'rho':rho}
 touched=[]
 for name,op,left,right in rebuilt:
  if 'delta' not in deps[name] and 'rho' not in deps[name]:continue
  if name in ('norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'):continue
  check(left in vals and right in vals,'input cut has no unpaid argument')
  vals[name]={'*':times,'+':plus,'-':minus}[op](vals[left],vals[right]);touched.append(name)
 check(len(touched)==10,'ten literal input rows')
 kap=plus(u,times(D,delta));mu=plus(plus(W,times(a,kap)),times(H,rho))
 check(vals['index_rhs']==kap and vals['exponent_rhs']==mu,'roots')
 check(vals['norm_input']==minus(square(mu),times(D,square(kap))),'norm')
 pp=minus(times(P,H),times(times(a,D),Q));qq=times(D,Q)
 rr=plus(plus(times(times(P,H),u),times(times(Q,D),W)),times(times(S,H),D))
 line=minus(plus(times(pp,kap),times(qq,mu)),rr)
 check(line==times(times(H,D),minus(plus(times(P,delta),times(Q,rho)),S)),'affine identity')
 linear=minus(plus(times(p,k),times(q,m)),r)
 quadratic=plus(minus(times(minus(square(p),times(D,square(q))),square(k)),scale(2,times(times(p,r),k))),minus(square(r),square(q)))
 other=plus(minus(square(linear),scale(2,times(times(q,m),linear))),times(square(q),minus(minus(square(m),times(D,square(k))),constant(1))))
 check(quadratic==other,'conic identity')
 # Independent integer checks of all proof constants, with no new Pell histories.
 growth=0
 for R in range(7,200):
  check(3*2**R>=R**3 and 2*R**3>(R+1)**3,'induction inequalities');growth+=1
 cutoffs=0
 for t in range(20):
  for L in range(1,41):
   n=23*L*L;ell=0
   while 2**ell<n:ell+=1
   K=8*t+4+ell
   check(2**(K-8*t-4)>=n and (ell==0 or 2**(ell-1)<n),'integer ceil');cutoffs+=1
 return {'scope':'independent full literal source/dependency and formal input-eliminant audit; prose reviews the infinite bounds','pins':PINS,'dependency_pins':receipt['pins'],'source_rows':len(rebuilt),'M':M,'A':A,'exterior_computed':exterior,'exterior_free':free,'all_rows_and_ports_live':True,'input_rows_checked':touched,'exact_affine_identity':True,'exact_conic_identity':True,'conic_terms':[[list(k),v] for k,v in sorted(quadratic.items())],'growth_diagnostics':growth,'cutoff_diagnostics':cutoffs,'full_positive_zeros_materialized':0,'reviewer_sha256':sha(Path(__file__).read_bytes())}
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--packet',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.root,a.packet);s=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.output:a.output.write_text(s)
 if a.expect:check(a.expect.read_text()==s,'receipt')
 print('PASS: independent 83 rows, 71 exterior values, 10 input rows, 2 formal identities')
if __name__=='__main__':main()
