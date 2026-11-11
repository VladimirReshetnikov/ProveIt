#!/usr/bin/env python3
import gzip,hashlib,json,math,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-anchor-cse';source=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();rec=json.loads((pkg/'result.json').read_bytes());assert sha(source)==rec['graph_sha256']=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(source.read_bytes());rows=g['source'];edges={r[0]:r for r in rows};assert len(rows)==65
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 z=(source.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'];data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['raw_sha256'];ports[name]=int.from_bytes(data,'big')
P=tuple(rec['moduli']);assert len(set(P))==3 and all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in P) and rec['samples_per_modulus']==4 and rec['seed']==0xA5C35E
rng=random.Random(0xA5C35E);mods=[p for p in P for _ in range(4)];inputs={x:tuple(rng.randrange(1,p) for p in mods) for x in g['witnesses']};inputs.update({name:tuple(x%p for p in mods) for name,x in ports.items()});inputs.update({i:(i,)*len(mods) for i in range(5)})
def ancestors(x):
 seen=set();stack=[x]
 while stack:
  v=stack.pop()
  if v in edges and v not in seen:seen.add(v);stack.extend(edges[v][2:])
 return seen
eligible=[r[0] for r in rows[:60] if r[0] not in ancestors('N1')];assert len(eligible)==37 and set(eligible)==set(rec['all']) and set(eligible).isdisjoint(ancestors('Delta')) and set(eligible)&ancestors('scaled_Ns')=={'f2','normalized_S','normalized_S2','scaled_f2','scaled_Ns'}
constants=0
for target in eligible:
 new=[[r[0],r[1]]+['anchor_scaled' if x==target else x for x in r[2:]] for r in rows]+[['anchor_scaled','*',target,'N1']];d={r[0]:r for r in new};vals=dict(inputs);active=set();done=set();ordered=[]
 def visit(x):
  if x not in d:return
  assert x not in active
  if x in done:return
  active.add(x);_,op,a,b=d[x];visit(a);visit(b);va,vb=vals[a],vals[b];vals[x]=tuple((u+v if op=='+' else u-v if op=='-' else u*v)%p for u,v,p in zip(va,vb,mods));active.remove(x);done.add(x);ordered.append(x)
 visit(g['output']);assert len(done)==66 and all(x in done for x in ('N1','Delta','anchor_scaled'))
 # In this run there are no gate/gate or gate/existing-leaf signature collisions at all.
 signatures=set(inputs.values())
 for x in ordered:
  assert vals[x] not in signatures;signatures.add(vals[x]);constants+=int(all(vals[x][4*k+j]==vals[x][4*k] for k in range(3) for j in range(4)))
 assert rec['all'][target]['before']==rec['all'][target]['after']==66 and not rec['all'][target]['aliases']
assert rec['eligible_count']==37 and not rec['candidate_below_65'] and not rec['candidate_below_66'] and rec['positive_control']['before']==66 and rec['positive_control']['after']==65 and rec['positive_control']['aliases']['duplicate_N0']=='N0'
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-main-norm-shear-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','variants':37,'constant_sample_signatures':constants,'scope':'N1 one-node scaling and existing-fingerprint CSE only; no global minimum or Lean theorem'},indent=2))
