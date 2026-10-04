"""Fresh read-only DAG recount and exact degree check. No upstream code imports."""
import collections, hashlib, json
from pathlib import Path
ROOT=Path('/workspace/shared/repeated-sandpile-report53-release-20261004')
OUT=Path('/workspace/shared/report53-manuscript-audit-20261004')
p=ROOT/'science/evidence/polynomial-dag.json'
j=json.loads(p.read_bytes())
gates=j['gates']; body=j['body_gate_count']; witnesses=j['witnesses']
assert len(set(witnesses))==len(witnesses)
assert j['input']=='InputPlus'
polys=[]
def add(a,b,sgn=1):
 c=a.copy()
 for m,v in b.items():
  c[m]=c.get(m,0)+sgn*v
  if c[m]==0: del c[m]
 return c
def mul(a,b):
 c={}
 for m,u in a.items():
  for n,v in b.items():
   k=tuple(sorted(m+n)); c[k]=c.get(k,0)+u*v
 return {m:v for m,v in c.items() if v}
def resolve(ref):
 k,v=ref.split(':',1)
 if k=='gate': return polys[int(v)]
 if k=='constant': return {():int(v)} if int(v) else {}
 if k=='witness':
  assert v in witnessset
  return {(ref,):1}
 assert k=='input' and v==j['input'],ref
 return {(ref,):1}
witnessset=set(witnesses)
for i,(op,a,b) in enumerate(gates):
 assert op in '+-*'
 for ref in (a,b):
  k,v=ref.split(':',1)
  if k=='gate': assert 0<=int(v)<i
  elif k=='witness': assert v in witnessset
  elif k=='input': assert v==j['input']
  else: assert k=='constant'; int(v)
 if i<body:
  x,y=resolve(a),resolve(b)
  polys.append(mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1))
residuals=[]; hist=collections.Counter(); top=[]
for a,b,name in j['equalities']:
 r=add(resolve(a),resolve(b),-1)
 deg=max(map(len,r),default=-1); hist[deg]+=1
 if deg==9: top.append({'name':name,'terms': [{'coefficient':c,'variables':list(m)} for m,c in r.items() if len(m)==9]})
 residuals.append((a,b,name))
# Exact SOS syntax, independent of any author's expression implementation.
idx=body; squares=[]; acc=None
for a,b,name in residuals:
 assert gates[idx]==['-',a,b]; ref=f'gate:{idx}'; idx+=1
 assert gates[idx]==['*',ref,ref]; sq=f'gate:{idx}'; idx+=1
 squares.append(sq)
acc=squares[0]
for sq in squares[1:]:
 assert gates[idx]==['+',acc,sq]; acc=f'gate:{idx}';idx+=1
assert idx==len(gates) and acc==j['output']
# Reachability, including every witness and input.
seen=set(); stack=[j['output']]
while stack:
 ref=stack.pop()
 if ref in seen: continue
 seen.add(ref)
 if ref.startswith('gate:'):
  stack.extend(gates[int(ref[5:])][1:])
assert all(f'gate:{i}' in seen for i in range(len(gates)))
assert all('witness:'+w in seen for w in witnesses)
assert 'input:'+j['input'] in seen
assert max(hist)==9 and hist[9]==3
expected=['witness:box.tx','witness:box.ty','witness:box.tz','witness:descriptor.d','witness:descriptor.e','witness:descriptor.f','witness:descriptor.p','witness:descriptor.q','witness:descriptor.r']
assert all(t['terms']==[{'coefficient':-4,'variables':expected}] for t in top)
result={'dag_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'positive_witnesses':len(witnesses),'residuals':len(residuals),'gates':len(gates),'body_gates':body,'body_operations':dict(collections.Counter(g[0] for g in gates[:body])),'sos_operations':dict(collections.Counter(g[0] for g in gates[body:])),'all_operations':dict(collections.Counter(g[0] for g in gates)),'ports':len(j['ports']),'macros':len(j['macros']),'macro_kinds':dict(collections.Counter(m['kind'] for m in j['macros'])),'residual_degree_histogram':dict(sorted(hist.items())),'degree_nine_residuals':top,'exact_total_degree':18,'top_sos_coefficient':48,'ordered_sos_verified':True,'all_reachable':True,'upstream_code_executed':False}
(OUT/'literal-dag-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
