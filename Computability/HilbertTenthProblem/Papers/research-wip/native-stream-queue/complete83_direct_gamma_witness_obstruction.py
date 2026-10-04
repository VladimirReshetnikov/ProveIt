#!/usr/bin/env python3
"""Bounded inert-data compiler for the seventeen direct main-quotient aliases."""
import argparse
import hashlib
import json
import random
from fractions import Fraction
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete83_independent_gamma_scout.md': 'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete83_independent_gamma_scout.json': 'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete83_multiplicative_gamma_obstruction.md': '012ba873b2cc4936e4d8865837a101d997b877dcc03e61c801cdb0cf010e527a',
 '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
 '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
}
GROUPS = {
 'small_outer': ['Jrep','F','alpha','transport_quotient','h','s','w','Z'],
 'large_native': ['f','i','auxiliary_quotient','tau_root','y_aux'],
 'opposite_parity': ['eta','zeta'],
 'input_coefficient_gap': ['delta'],
 'equal_projection_boundary': ['rho'],
}

def require(ok, message):
 if not ok:
  raise ValueError(message)

def digest(value):
 return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def trim(poly):
 while len(poly)>1 and poly[-1]==0:
  poly.pop()
 return poly

def poly_add(a,b,sign=1):
 out=a.copy()+[0]*max(0,len(b)-len(a))
 for j,x in enumerate(b):
  out[j]+=sign*x
 return trim(out)

def poly_mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):
   out[j+k]+=x*y
 return trim(out)

def evaluate(rows,values):
 out=values.copy()
 for name,op,l,r in rows:
  a=out[l] if isinstance(l,str) else l
  b=out[r] if isinstance(r,str) else r
  out[name]=a*b if op=='*' else a+b if op=='+' else a-b
 return out

def pell(A,n):
 # Fresh binary pair exponentiation, used only for small subsystem diagnostics.
 D=A*A-1
 def times(a,b):
  return (a[0]*b[0]+D*a[1]*b[1], a[0]*b[1]+a[1]*b[0])
 out=(1,0); base=(A,1)
 while n:
  if n&1:
   out=times(out,base)
  base=times(base,base); n//=2
 return out

def build(root):
 for name,pin in PINS.items():
  require(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'pin '+name)
 parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
 rows=parent['source']
 require([r for r in rows if 'gamma_sum' in r[2:]]==[['gam','*','gamma_sum','a4m5']],'private consumer')
 require([r for r in rows if 'sigma' in r[2:]]==[['gamma_sum','+','rho','sigma']],'sigma consumer')
 witnesses=[v for v in parent['witnesses'] if v!='sigma']
 free=[v for v in parent['free'] if v!='sigma']
 aliases=[v for group in GROUPS.values() for v in group]
 require(len(aliases)==17 and len(set(aliases))==17 and set(aliases)==set(witnesses),'exact grammar')
 rng=random.Random(830017)
 forms=[]; all_value_count=0; equalities=0
 for v in witnesses:
  source=[(['gam','*',v,'a4m5'] if r[0]=='gam' else r.copy()) for r in rows if r[0]!='gamma_sum']
  require([r for r in source if r[0]!='gam']==[r for r in rows if r[0] not in ('gam','gamma_sum')],'retained rows')
  known=set(free); degrees={x:0 if x in parent['fixed_numerals'] else 1 for x in free}
  for name,op,l,r in source:
   require(name not in known and op in ('+','-','*'),'source names/operations')
   require(all(not isinstance(x,str) or x in known for x in (l,r)),'source closure')
   dl=degrees[l] if isinstance(l,str) else 0; dr=degrees[r] if isinstance(r,str) else 0
   degrees[name]=dl+dr if op=='*' else max(dl,dr); known.add(name)
  live={parent['output']}
  for name,op,l,r in reversed(source):
   require(name in live,'dead gate '+name)
   live.update(x for x in (l,r) if isinstance(x,str))
  require(set(free)<=live,'dead free port')
  M=sum(r[1]=='*' for r in source)
  require((len(source),M,len(source)-M,len(witnesses),len(free))==(83,47,36,17,24),'ledger')
  # Coefficient cut: rho + (v-rho) = v, including the collision v=rho.
  cut={}
  for variable,coefficient in [('rho',1),(v,1),('rho',-1)]:
   cut[variable]=cut.get(variable,0)+coefficient
  require({a:b for a,b in cut.items() if b}=={v:1},'all-ring private cut')
  for trial in range(16):
   values={x:Fraction(rng.randrange(-4,6),rng.randrange(1,5)) if trial<8 else rng.randrange(-4,6) for x in free}
   previous=values.copy(); previous['sigma']=values[v]-values['rho']
   actual=evaluate(source,values); expected=evaluate(rows,previous)
   for name,_,_,_ in source:
    require(actual[name]==expected[name],'all-value retained register '+name)
    equalities+=1
   all_value_count+=1
  dense=[]
  for prime,beta,ell in [(1000000007,15,10),(1000000009,31,50)]:
   constants={'Bm1':beta,'Kconstant':7,'twice_cell_bits':ell,'inner_bits':5,'MC':6,'MF':19}
   env={x:[constants[x]] if x in constants else [0,1] for x in free}
   for name,op,l,r in source:
    a=env[l] if isinstance(l,str) else [l]; b=env[r] if isinstance(r,str) else [r]
    poly=poly_mul(a,b) if op=='*' else poly_add(a,b,1 if op=='+' else -1)
    env[name]=trim([c%prime for c in poly])
   factor_degrees=[len(env[x])-1 for x in parent['factors']]
   require(factor_degrees==[22,18,32,60,7,2,46],'factor degrees')
   result=env[parent['output']]
   leader=-(1<<18)*(ell+3)*pow(beta,111,prime)%prime
   require(len(result)==188 and result[-1]==leader,'full diagonal degree/leader')
   dense.append({'prime':prime,'diagnostic_constants':constants,'factor_degrees':factor_degrees,'exact_degree':187,'leading_coefficient':leader,'coefficients_sha256':digest(result)})
  forms.append({'alias_port':v,'exclusion_group':next(k for k,vs in GROUPS.items() if v in vs),'source':source,'source_sha256':digest(source),'output':parent['output'],'factors':parent['factors'],'free':free,'witnesses':witnesses,'witness_domain':parent['witness_domain'],'ordinary_input':parent['ordinary_input'],'fixed_numerals':parent['fixed_numerals'],'ledger':{'multiplications':47,'additions_subtractions':36,'total':83,'positive_witnesses':17},'exact_degree':187,'naive_degree':degrees[parent['output']],'all_ring_pullback':'sigma_parent='+v+'-rho','positive_status':'EMPTY on every inherited valid compiler slice','dense_diagnostics':dense})
 # Independent small Pell components check the strict quotient sandwich and rank-size inequality.
 components=[]
 for A in range(3,9):
  for R in (3,7,11):
   D,c=pell(A,R); _,prev=pell(A,R-1)
   H=4*A-5; X=2**R; numerator=D-(A-2)*c-X
   require(numerator%H==0,'projection integrality')
   gamma=numerator//H
   # These small components are not native: use the exact inequality X<2*prev,
   # which suffices for the lower sandwich and holds for these cases.
   require(X<2*prev and prev<gamma<c and gamma*H<2*c,'quotient sandwich')
   require(2*(A*A-1)<A*H,'delta-gap upper coefficient')
   for u in range(1,A):
    kappa=u+gamma*(A*A-1)
    require(c<kappa<A*c+D,'Pell coefficient gap')
   item={'A':A,'R':R,'c_bits':c.bit_length(),'gamma_bits':gamma.bit_length()}
   if R==3:
    f,z=pell(A,R*c)
    require(z%(c*c)==0,'rank divisibility')
    i=z//(c*c)
    require(f>c*c and i>c,'strong sizes')
    item.update({'m':R*c,'f_bits':f.bit_length(),'i_bits':i.bit_length()})
   components.append(item)
 return {'schema':'current83-direct-witness-alias-obstruction-v1','pins':PINS,'grammar':{'ports':witnesses,'groups':GROUPS,'only_removed_gate':'gamma_sum','only_changed_retained_gate':'gam','only_removed_witness':'sigma','other_rows_unchanged':True,'scope':'Only direct identification with one of the other seventeen supplied positive witness ports; no nonlinear reuse or arbitrary-circuit lower bound'},'forms':forms,'evidence':{'full_sources':17,'live_gates_total':1411,'all_value_assignments':all_value_count,'retained_register_equalities':equalities,'small_noncompiler_pell_components':components,'full_positive_compiler_zeros_materialized':False},'uniform_leader':'32*Q^111*h*alias_port*delta^2*i^4*(eta+zeta)^13*w^18*s^31*Nt_top*T^2*f^2','uniform_diagonal_coefficient':'-2^18*(twice_cell_bits+3)*Bm1^111'}

def typed_equal(a,b):
 if type(a) is not type(b):
  return False
 if isinstance(a,dict):
  return a.keys()==b.keys() and all(typed_equal(a[k],b[k]) for k in a)
 if isinstance(a,list):
  return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
 return a==b

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',type=Path,required=True)
 group=parser.add_mutually_exclusive_group(required=True)
 group.add_argument('--output',type=Path)
 group.add_argument('--expect',type=Path)
 args=parser.parse_args(); receipt=build(args.root)
 if args.output:
  args.output.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 else:
  require(typed_equal(receipt,json.loads(args.expect.read_text())),'receipt mismatch')
 print('PASS: 17 complete direct-alias charts; each 83=47M36A, 17w, degree187; positive slices empty by companion proof')

if __name__=='__main__':
 main()
