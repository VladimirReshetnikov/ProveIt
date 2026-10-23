#!/usr/bin/env python3
"""New authored finite audits. These do not prove unbounded solvability."""
from pathlib import Path
from collections import Counter
from itertools import product, combinations_with_replacement
from math import isqrt
import json,random,hashlib,gzip
ROOT=Path(__file__).resolve().parent

def poly_value(terms,ports,mod=None):
 ans=0
 for t in terms:
  a=t['coefficient']
  for p,e in zip(ports,t['powers']):a*=pow(p,e,mod) if mod else p**e
  ans+=a
 return ans%mod if mod else ans

def eval_dag(obj,vals,ports,mod):
 fixed={r['name']:poly_value(r['terms'],ports,mod) for r in obj['coefficient_recipes']};fixed['base_floor']=pow(2,obj['base_floor_exponent'],mod)
 out=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='variable':v=vals[n['name']]
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  else:
   a,b=out[n['left']],out[n['right']];v=a+b if k=='add' else a-b if k=='sub' else a*b
  out.append(v%mod)
 return out[obj['output']],{k:out[i] for k,i in obj['named_nodes'].items()}

def degree_audit(obj,ports):
 fixed={r['name']:poly_value(r['terms'],ports) for r in obj['coefficient_recipes']};fixed['base_floor']=1
 out=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='variable':a=(1,1)
  elif k in ('literal','fixed'):
   val=n['value'] if k=='literal' else fixed[n['name']];a=(0,val) if val else (-1,0)
  else:
   (da,ca),(db,cb)=out[n['left']],out[n['right']]
   if k=='mul':a=(da+db,ca*cb) if ca and cb else (-1,0)
   else:
    if k=='sub':cb=-cb
    a=(da,ca) if da>db else (db,cb) if db>da else (da,ca+cb)
    if a[1]==0:
     if a[0]>0:raise AssertionError(('unresolved leading cancellation',n,a))
     a=(-1,0)
  out.append(a)
 return out[obj['output']],{k:out[i] for k,i in obj['named_nodes'].items()}

def factor_norm(a0,a1,V0,V1,u,v,m,M,n):
 O=u*m;T=u*(n+M)+v-O*(2*M+V0*V1)
 return (T*T-O*O*(a0+V0*V0*a1))**2-4*O**4*V0*V0*a0*a1

def main():
 if not __debug__:raise RuntimeError('Optimized Python disables assertions')
 objects={}
 for dom in ['positive','natural']:
  for cert in ['', '_degree_certificate']:
   name='multitarget_nine_'+dom+cert;obj=json.loads((ROOT/'generated'/f'{name}.json').read_text());objects[name]=obj
   assert len(obj['variables'])==9
   assert sum(Counter(n['kind'] for n in obj['nodes'] if 'left'in n).values())==obj['total_operations']
   assert obj['degree']==162444*obj['W']+83224
 weights=objects['multitarget_nine_positive']['weights'];codes={}
 for k in range(3):
  for a in combinations_with_replacement(range(31),k):
   t=sum(weights[i] for i in a);assert t not in codes;codes[t]=a
 assert len(codes)==528
 count=0
 rng=random.Random(381928)
 for mod in [1000000007,1000000009,2147483647]:
  for _ in range(60):
   vals={n:rng.randrange(1,1000) for n in objects['multitarget_nine_positive']['variables']};ports=[rng.randrange(1,10000) for _ in range(4)]
   v,named=eval_dag(objects['multitarget_nine_positive'],vals,ports,mod)
   vc,_=eval_dag(objects['multitarget_nine_positive_degree_certificate'],vals,ports,mod);assert v==vc
   shifted={n:x-1 for n,x in vals.items()}
   vn,_=eval_dag(objects['multitarget_nine_natural'],shifted,ports,mod);assert v==vn
   count+=1
 instance=json.loads((ROOT/'MULTITARGET_INSTANCE.json').read_text());actual_ports=[]
 for r in instance['four_ports']:
  path=ROOT.parent/r['file'];raw=gzip.decompress(path.read_bytes());assert hashlib.sha256(raw).hexdigest()==r['raw_sha256'];actual_ports.append(int.from_bytes(raw,'little'))
 obj=objects['multitarget_nine_positive'];fixed_expected={r['name']:poly_value(r['terms'],actual_ports) for r in obj['coefficient_recipes']};fixed_expected['base_floor']=1<<obj['base_floor_exponent']
 assert all(abs(x)<(1<<obj['coefficient_bound_power_of_two']) for n,x in fixed_expected.items() if n!='base_floor')
 for r in instance['fixed_payloads']:
  path=ROOT/r['file'];raw=gzip.decompress(path.read_bytes());assert hashlib.sha256(raw).hexdigest()==r['raw_sha256'];value=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1);assert value==fixed_expected[r['name']]
 for mod in [1000000007,1000000009,2147483647]:
  for _ in range(5):
   vals={n:rng.randrange(1,100) for n in obj['variables']};v,_=eval_dag(obj,vals,[x%mod for x in actual_ports],mod);vc,_=eval_dag(objects['multitarget_nine_positive_degree_certificate'],vals,[x%mod for x in actual_ports],mod);assert v==vc
 degree_records=[]
 for ports in [(2,3,5,7),(19,23,29,31),(101,103,107,109)]:
  (degree,leader),names=degree_audit(objects['multitarget_nine_positive_degree_certificate'],ports)
  assert degree==129875980,(degree,129875980)
  assert leader==2**2050,leader
  degree_records.append({'ports':ports,'degree':degree,'leader_power_of_two':2050,'named_degrees':{k:v[0] for k,v in names.items()}})
 # Finalizer completeness and m=0 exclusion, including signed divisors.
 fixtures=0
 for r0,r1,u,m in product(range(1,5),range(1,5),[-3,-1,1,2],[1,2]):
  a0,a1=r0*r0,r1*r1;V0,V1=r0+1,r1+1;M=4;v=2*u
  Z=2*M+V0*V1+r0+V0*r1;n=m*Z-M-v//u
  assert n>=0 and factor_norm(a0,a1,V0,V1,u,v,m,M,n)==0;fixtures+=1
 for a0,a1,u,n in product(range(1,8),range(1,8),[-3,-1,1,2],range(5)):
  assert factor_norm(a0,a1,8,8,u,2*u,0,4,n)!=0
 # Direct coefficient extraction at every target for a small genuine base.
 targetdata=json.loads((ROOT.parent/'quartic/QUADRATIC_TARGETS.json').read_text())
 import sympy as s
 pp=s.symbols('beta K0 MC MF');pmap=dict(zip(targetdata['ports'],pp));sourcepoints=0
 for ports in [(2,3,5,7),(11,13,17,19)]:
  for _ in range(8):
   zs=[rng.randrange(4) for _ in range(31)]
   C={0:1}
   for w,z in zip(weights,zs):C[w]=z
   C2={}
   for i,a in C.items():
    for j,b in C.items():C2[i+j]=C2.get(i+j,0)+a*b
   D={}
   rows=[]
   for row in targetdata['rows']:
    val=0
    for t in row['terms']:
     co=int(s.sympify(t['weighted_coefficient'],locals=pmap).subs(dict(zip(pp,ports))));exp=t['encoding_exponent'];assert exp not in D;D[exp]=co
     raw=int(s.sympify(t['coefficient'],locals=pmap).subs(dict(zip(pp,ports))));term=raw
     for z,e in zip(zs,t['alpha']):term*=z**e
     val+=term
    rows.append(val)
   for row,want in zip(targetdata['rows'],rows):
    got=sum(co*C2.get(row['target_exponent']-exp,0) for exp,co in D.items());assert got==2*want
    sourcepoints+=1
 report={'status':'PASS','nine_variable_domains':2,'B2_sums_checked':528,'modular_circuit_and_domain_replays':count,'actual_tuple_modular_replays':15,'actual_fixed_payloads_reconstructed':len(instance['fixed_payloads']),'degree_replays':degree_records,'finalizer_completeness_fixtures':fixtures,'zero_margin_exclusions':49*4*5,'coefficient_extraction_targets':sourcepoints,'limitations':'Finite audits only; unbounded equivalence and uniform degree require accompanying mathematical proof.'}
 (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='degree_replays'}))
if __name__=='__main__':main()

