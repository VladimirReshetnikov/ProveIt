#!/usr/bin/env python3
"""Independent exact checker: no producer import; standard library only.

Certify local ring identities from literal parent/child graphs, then propagate
node equality to the full output. No modular tests are used for identity.
"""
from pathlib import Path
from collections import Counter
import json,hashlib,gzip,sys
HERE=Path(__file__).resolve().parent
CASES=[
 ('positive10_98_degree368','candidates/ten-positive-zero-offset/equation.json','047ea8145ef52ab939322f2147c75272e7a182016be78a453fbdf2d3c2a6a493',98,368,[('Znum',{'P1','P1mu2'})]),
 ('positive10_direct103_degree340','candidates/ten-positive-direct-zero-offset/equation.json','bea07edb73ff6cdf8f0f7c45dec63fa96b42848066cdb82661fd1e9fd4cd282f',103,340,[('Znum',{'P1','P1mu2','q4'})]),
 ('positive11_107_degree211','candidates/positive11-adaptive-shears/positive11.json','b1c40ea68dcc20c5609cc279e5e7767bf347c184c32ca75183df45f3a510fcb1',107,211,[('U',{'q2','S'}),('g71',{'E','S'}),('Zbar',{'M'}),('N8',set())]),
 ('positive12_95_degree70','candidates/free-j-polarized-positive/equation.json','2a8da9ac141de5078fbdca96acccab5a7c44f6b39f4bc6063261b29179cb68be',95,70,[('Z',{'M'})]),
 ('positive13_87_degree51','candidates/free-j-polarized-positive/source/positive/p13_free_J.json','a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8',87,51,[('Z',{'M'})]),
]
def need(value,message):
 if not value:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def load(path):return json.loads(path.read_bytes())
# Distinct implementation: polynomials are maps from sorted monomial tuples to integers.
def add(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+sign*c
 return {m:c for m,c in out.items()if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items()if c}
def literal(n):return {():n}if n else{}
def topology(d):
 known=set(d['witnesses']+d['fixed_numerals']);defs={}
 degree={v:1 for v in d['witnesses']}|{v:0 for v in d['fixed_numerals']}
 for n,op,a,b in d['source']:
  need(n not in known and op in ['+','-','*'],'fresh ring gate '+n)
  need(all(type(x)is int or x in known for x in [a,b]),'acyclic operands '+n)
  da,db=[0 if type(x)is int else degree[x]for x in [a,b]]
  degree[n]=da+db if op=='*'else max(da,db);defs[n]=(op,a,b);known.add(n)
 live=set();todo=[d['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in defs:todo.extend(defs[n][1:])
 need(known==live,'complete liveness')
 count=dict(Counter(row[1]for row in d['source']))
 need(d['operation_breakdown']==count and d['operations']==len(defs),'literal count metadata')
 return defs,count,degree[d['output']]
def prove_complete(parent,child,cuts):
 pd,_,_=topology(parent);cd,counts,raw_degree=topology(child)
 need(parent['witnesses']==child['witnesses'] and parent['fixed_numerals']==child['fixed_numerals'],'all inputs/ports unchanged')
 need(parent['domain']==child['domain']=='strictly positive integers','same witness domain')
 need(parent['output']==child['output'],'same output name')
 certified=set(parent['witnesses']+parent['fixed_numerals'])
 def propagate():
  while True:
   todo=[]
   for n,definition in pd.items():
    if n in certified or cd.get(n)!=definition:continue
    if all(type(x)is int or x in certified for x in definition[1:]):todo.append(n)
   if not todo:return
   certified.update(todo)
 def expand(n,defs,excluded,memo):
  if type(n)is int:return literal(n)
  if n in memo:return memo[n]
  if n in certified and n not in excluded:return {(n,):1}
  need(n in defs,'unproved cut reaches a missing leaf '+n)
  op,a,b=defs[n];a=expand(a,defs,excluded,memo);b=expand(b,defs,excluded,memo)
  memo[n]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else-1)
  return memo[n]
 propagate();cut_records=[]
 for target,excluded in cuts:
  a=expand(target,pd,excluded,{});b=expand(target,cd,excluded,{})
  need(a==b,'exact free polynomial cut '+target)
  certified.add(target);propagate();cut_records.append({'register':target,'collected_terms':len(a),'expanded_shared_nodes':sorted(excluded)})
 need(parent['output'] in certified,'complete output equality by structural induction')
 return {'operations':len(cd),'breakdown':counts,'syntactic_degree':raw_degree,'cuts':cut_records}
def main():
 pins=load(HERE/'SOURCE_PINS.json')
 need(pins['commit']=='84e16e43092614bae262ca59651cb9d77e31a255','fixed snapshot')
 for row in pins['sources']:need(sha((HERE/row['local_path']).read_bytes())==row['sha256'],'source byte pin '+row['local_path'])
 binding=load(HERE/'coefficients/BINDING.json');coeffs={}
 for name,pin in binding['ports'].items():
  rawzip=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(rawzip)
  need(sha(rawzip)==pin['sha256_gzip']and sha(raw)==pin['sha256_raw'],'complete coefficient payload '+name)
  v=int.from_bytes(raw,'little');need(v.bit_length()==pin['bits']and len(raw)==pin['raw_bytes'],'coefficient encoding '+name);coeffs[name]=v
 need(coeffs['beta']==2**590069-1,'literal beta specification')
 need(0<coeffs['MC']<coeffs['beta']<coeffs['MF']<2*coeffs['beta']and coeffs['K0']>0,'retained port box')
 receipts=[]
 for name,path,digest,count,degree,cuts in CASES:
  raw=(HERE/'parents'/path).read_bytes();need(sha(raw)==digest,'hardcoded full parent pin '+name)
  parent=json.loads(raw);child=load(HERE/'circuits'/(name+'.json'))
  need(child['parent_sha256']==digest,'child parent binding')
  need(child['coefficient_binding']=='../coefficients/BINDING.json','portable complete coefficient binding')
  result=prove_complete(parent,child,cuts)
  need(result['operations']==count and child['exact_degree']==parent['exact_degree']==degree,'count/degree transport metadata')
  # A changed final scalar or sign cannot pass full-output structural induction.
  import copy
  corrupted=copy.deepcopy(child);corrupted['source'][-1][1]='-'if corrupted['source'][-1][1]=='+'else'+'
  corrupted['operation_breakdown']=dict(Counter(r[1]for r in corrupted['source']))
  rejected=False
  try:prove_complete(parent,corrupted,cuts)
  except ValueError:rejected=True
  need(rejected,'reject changed final output')
  result.update(name=name,exact_degree=degree,identity='proved pointwise over every commutative ring',child_sha256=sha((HERE/'circuits'/(name+'.json')).read_bytes()),altered_output_rejected=True)
  receipts.append(result)
 output={'status':'PASS','optimized':bool(sys.flags.optimize),'coefficients':'all four complete gzip/raw payloads verified','degree_scope':'exact degree transported through pointwise identity from the pinned parent; no independent reproof of inherited native calibration','cases':receipts}
 target=HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json');target.write_text(json.dumps(output,indent=2)+'\n')
 print(json.dumps(output,indent=2))
if __name__=='__main__':main()
