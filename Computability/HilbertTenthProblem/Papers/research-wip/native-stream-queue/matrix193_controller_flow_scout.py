#!/usr/bin/env python3
"""Fresh complete-source controller-flow rewrite; all parents are inert bytes."""
import argparse,copy,hashlib,json,random
from pathlib import Path
from collections import Counter
PINS={
'matrix193_composed_output_scout.py':'e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317',
'matrix193_composed_output_scout.json':'a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37',
'matrix193_composed_output_scout.md':'83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748'}
def ck(t,m):
 if not t:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):
 def obj(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(v):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def algebra(B,J,EL,ES):
 z=(0,)*4
 def c(v):return {z:v} if v else {}
 def a(p,q,s=1):
  r=dict(p)
  for e,v in q.items():r[e]=r.get(e,0)+s*v
  return {e:v for e,v in r.items() if v}
 def m(p,q):
  r={}
  for e,v in p.items():
   for f,w in q.items():
    g=tuple(x+y for x,y in zip(e,f));r[g]=r.get(g,0)+v*w
  return {e:v for e,v in r.items() if v}
 atoms=[{tuple(int(k==j) for k in range(4)):1} for j in range(4)]
 b,j,l,s=atoms;bm=a(b,c(1),-1);P=a(m(bm,j),c(1));dst=a(j,l,-1)
 old=a(a(a(dst,s,-1),P),m(b,dst),-1);new=a(a(m(bm,l),c(1)),s,-1)
 ck(old==new,'integer polynomial flow identity')
 return {'formal_inputs':[B,J,EL,ES],'terms':[[list(e),v] for e,v in sorted(new.items())],
 'identity':'(J-EL-ES)+((B-1)*J+1)-B*(J-EL)=1+(B-1)*EL-ES'}

def graph(p):
 known=set(p['free']);deps={};counts=Counter();deg={s:int(s not in p['fixed_numerals']) for s in known}
 for n,op,l,r in p['source']:
  ck(n not in known and op in ['+','-','*'],'unique legal producer')
  ck(all(type(v)is int or type(v)is str and v in known for v in [l,r]),'closure')
  known.add(n);deps[n]=[l,r];counts[op]+=1
  deg[n]=deg.get(l,0)+deg.get(r,0) if op=='*' else max(deg.get(l,0),deg.get(r,0))
 todo=[p['output']];live=set()
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'all row and port liveness')
 return {'total':len(p['source']),'M':counts['*'],'A':counts['+']+counts['-'],'positive_witnesses':len(p['witnesses']),
 'proved_exact_degree':p['ledger']['proved_exact_degree'],'syntactic_degree_upper':deg[p['output']],
 'residuals':len(p['comparisons']),'all_live':True,'literal_count':len({v for r in p['source'] for v in r[2:] if type(v)is int})}

def transform(old):
 p=copy.deepcopy(old);by={r[0]:r for r in old['source']};B=old['ports']['B'];J=old['ports']['J'];P=old['ports']['P'];EL,ES=old['ports']['raw_edges'];left,right=old['comparisons'][-2]
 ck(by[P][1]=='+' and by[P][3]==1,'P affine definition');prod=by[P][2]
 ck(by[prod][1]=='*' and by[prod][3]==J,'P product');bm=by[prod][2];ck(by[bm][1:]==['-',B,1],'paid B minus one')
 ck(by[left][1]=='+' and by[left][3]==P,'flow left');src=by[left][2]
 ck(by[src][1]=='-' and by[src][3]==ES,'source sum');dst=by[src][2]
 ck(by[dst][1:]==['-',J,EL] and by[right][1:]==['*',B,dst],'flow right')
 removed={src,dst,left,right};first=min(i for i,r in enumerate(old['source']) if r[0] in removed)
 tail=old['source'][-62:];flow_residual=tail[36][0]
 ck(tail[36][1:]==['-',left,right],'full flow residual position')
 for n,op,l,r in old['source']:
  if n not in removed and n!=flow_residual:ck(l not in removed and r not in removed,'no extra flow consumer')
 extra=[['flow_scaled_load','*',bm,EL],['flow_switch_position','+','flow_scaled_load',1]]
 ck(not ({r[0] for r in extra}&set(by)),'new names')
 rows=[]
 for i,row in enumerate(old['source']):
  if i==first:rows.extend(extra)
  if row[0] in removed:continue
  rows.append([flow_residual,'-','flow_switch_position',ES] if row[0]==flow_residual else row[:])
 p['source']=rows;p['comparisons'][-2]=['flow_switch_position',ES];p['stage_counts']['outer_producers']-=2;p['ledger']=graph(p)
 ck(p['ledger']['total']==old['ledger']['total']-2 and p['ledger']['M']==old['ledger']['M'] and p['ledger']['A']==old['ledger']['A']-2,'full saving')
 # The changed residual is exactly equal; use it as one proved formal atom.
 intern={};counter=[0]
 def ident(k):
  if k not in intern:intern[k]=counter[0];counter[0]+=1
  return intern[k]
 def expand(source):
  env={s:ident(('free',s)) for s in old['free']}
  for n,op,l,r in source:
   aa=ident(('int',l)) if type(l)is int else env[l];bb=ident(('int',r)) if type(r)is int else env[r]
   env[n]=ident(('proved_flow_residual',)) if n==flow_residual else ident((op,aa,bb))
  return env
 a=expand(old['source']);b=expand(rows)
 for n,op,l,r in old['source']:
  if n not in removed:ck(a[n]==b[n],'full retained expression '+n)
 ck(a[old['output']]==b[p['output']],'entire output identity')
 return p,{'removed_rows':[r for r in old['source'] if r[0] in removed],'new_rows':extra,'residual_wire':flow_residual,
 'exact_local_identity':algebra(B,J,EL,ES),'retained_rows_checked':len(old['source'])-4,
 'full_relation':'F_flow=F_composed on identical supplied coordinates'}

def evaluate(p,v,mod):
 env=dict(v)
 for n,op,l,r in p['source']:
  a=env[l] if type(l)is str else l;b=env[r] if type(r)is str else r
  env[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%mod
 return env

def run(root):
 for n,pin in PINS.items():ck(sha((root/n).read_bytes())==pin,'pin '+n)
 old=read(root/'matrix193_composed_output_scout.json');packets=[];proofs=[];samples=[]
 for parent in old['packets']:
  p,proof=transform(parent);rng=random.Random(1677+p['n']);numbers=[]
  for modulus in [1000000007,1000000009]:
   for case in range(16):
    v={s:rng.randrange(-100,101) for s in p['free']}
    if case%2==0:v.update(p['fixture_fixed_bindings'])
    a=evaluate(parent,v,modulus);b=evaluate(p,v,modulus)
    for n in a.keys()&b.keys():ck(a[n]==b[n],'entire retained row modular value')
    numbers.append({'modulus':modulus,'case':case,'output':b[p['output']]})
  packets.append(p);proofs.append(proof);samples.append(numbers)
 ck([(p['ledger']['total'],p['ledger']['M'],p['ledger']['A']) for p in packets]==[(301,126,175),(1677,801,876)],'exact final ledgers')
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'full_identities':proofs,'modular_checks':samples,
 'scope':{'same_positive_witnesses':True,'all_ring_identity':True,'inherited_exact_degrees':[1363,35587],
 'ordinary_input_and_fixed_recipe':'unchanged through identical complete polynomial','predecessor_code_executed':False,'new_native_or_giant_outer_fixture_claim':False,'universal84_unchanged':True}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root)
 if a.write:a.write.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 else:ck(exact(r,read(a.expect)),'type-exact receipt')
 print(json.dumps({'status':'PASS','ledgers':[p['ledger'] for p in r['packets']]}))
if __name__=='__main__':main()
