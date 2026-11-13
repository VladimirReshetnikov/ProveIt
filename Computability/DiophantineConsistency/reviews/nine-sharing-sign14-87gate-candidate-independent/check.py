#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-87gate-candidate';old=root/'research/nine-sharing-sign14-88gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='5c928699b03a1f805d5be0cf3b2b5db2cdea43bbce1ad01d0f36875a8139c2b0'
assert sha(p/'seed.json')=='a2d509d3e5b693f3b0f4bb994eeb7e60e32c5ca2937206179599d574e7103998' and sha(p/'build.py')=='1a28784137a5bc5b212fa0a50448b71825eb0d280a4208df9b6d4a50ac76ac1a' and sha(p/'result.json')=='8b17089e41e1f1c033c944a60e63fe85e2c4be34db1c0a8c4779f443012e3747'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));x=m(a(port('K0'),a(v(9),n(1))),s(s(b,v(2)),a(v(3),n(1))));src=s(a(x,s(s(b,v(2)),n(1))),m(a(v(4),n(1)),b));dst=s(s(s(x,v(2)),n(1)),m(v(4),b));hits=[0]
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
one={():1};X={('X',):1};B={('B',):1};I={('I',):1};Z={('Z',):1};assert add(add(X,add(add(B,I,-1),one,-1)),mul(add(Z,one),B),-1)==add(add(add(X,I,-1),one,-1),mul(Z,B),-1)
assert before['residuals'][2]['gate']=='Nt' and tup(before['residuals'][2]['expr'])==src
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==78 and len(live)==87 and counts=={'add':32,'mul':38,'sub':17} and r['gate_counts']==counts and r['live_gates']==87 and r['residual_gates']==78
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-88gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
