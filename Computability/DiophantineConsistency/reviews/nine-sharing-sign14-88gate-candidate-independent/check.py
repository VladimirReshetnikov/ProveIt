#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-88gate-candidate';old=root/'research/nine-sharing-sign14-89gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='538751512c39c0e1ec416f784e910163dbb87b262bd91150d4f4f4b3dbff3a0e'
assert sha(p/'seed.json')=='5c928699b03a1f805d5be0cf3b2b5db2cdea43bbce1ad01d0f36875a8139c2b0' and sha(p/'build.py')=='05085e40b6c14a5dff70e8eb6bdd85830afd07bdbb1162c9f5e26524c0602f9d' and sha(p/'result.json')=='b9d781d3b536f93bd7720bd026fb3d141e31cdd75f62291ad9f570f80e6a4c30'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));src=s(b,a(v(2),n(1)));dst=s(s(b,v(2)),n(1));hits=[0]
def change(x):
 if x==src:hits[0]+=1;return dst
 if x[0] in ('add','sub','mul'):return (x[0],change(x[1]),change(x[2]))
 return x
roots=[change(tup(row['expr'])) for row in before['residuals']];assert hits[0]==1==r['identity_occurrences'];assert len(roots)==5==len(after['residuals']) and all(tup(row['expr'])==roots[i] and row['gate']==before['residuals'][i]['gate'] for i,row in enumerate(after['residuals']))
# Independently normalize the distributive identity in the free commutative ring.
def add(x,y,sgn=1):
 z=x.copy()
 for k,val in y.items():z[k]=z.get(k,0)+sgn*val
 return {k:val for k,val in z.items() if val}
def mul(x,y):
 z={}
 for k,val in x.items():
  for l,w in y.items():key=tuple(sorted(k+l));z[key]=z.get(key,0)+val*w
 return {k:val for k,val in z.items() if val}
one={():1};B={('B',):1};I={('I',):1};assert add(B,add(I,one),-1)==add(add(B,I,-1),one,-1)
def contains(t,target):return t==target or (t[0] in ('add','sub','mul') and (contains(t[1],target) or contains(t[2],target)))
assert before['residuals'][2]['gate']=='Nt' and contains(tup(before['residuals'][2]['expr']),src) and any(contains(tup(row['expr']),s(b,v(2))) for i,row in enumerate(before['residuals']) if i!=2)
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==79 and len(live)==88 and counts=={'add':34,'mul':38,'sub':16} and r['gate_counts']==counts and r['live_gates']==88 and r['residual_gates']==79
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-89gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
