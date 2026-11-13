#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-86gate-candidate';old=root/'research/nine-sharing-sign14-87gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='a2d509d3e5b693f3b0f4bb994eeb7e60e32c5ca2937206179599d574e7103998'
assert sha(p/'seed.json')=='c397c797e39f54bbe4e2a621a15cd94a898a6b44604379aae28a21f0d5861497' and sha(p/'build.py')=='4981b66db20c5f87f6fc1214b2a61990de4353052bcb5458805261a9fbfd0bf8' and sha(p/'result.json')=='bc5438b639776efb420b16faa8cdfc84c4f82f688271d0bc1b1ce764c0a9efec'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));q=a(b,n(1));rank=a(m(b,s(b,v(2))),a(v(3),n(1)));R=a(m(rank,m(q,q)),m(a(port('MC'),m(q,port('MF'))),a(v(1),n(1))));hits=[0];changed=[]
def change(x):
 if x[0]=='sub' and x[1][0]=='add' and x[1][2]==rank and x[2]==R:
  hits[0]+=1;changed.append(x[1][1]);return s(change(x[1][1]),s(R,rank))
 if x[0] in ('add','sub','mul'):return (x[0],change(x[1]),change(x[2]))
 return x
roots=[change(tup(row['expr'])) for row in before['residuals']];assert hits[0]==4==r['identity_occurrences'] and len(set(changed))==2;assert len(roots)==5==len(after['residuals']) and all(tup(row['expr'])==roots[i] and row['gate']==before['residuals'][i]['gate'] for i,row in enumerate(after['residuals']))
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
A={('A',):1};R0={('R',):1};T={('T',):1};assert add(add(A,R0),T,-1)==add(A,add(T,R0,-1),-1)
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==77 and len(live)==86 and counts=={'add':30,'mul':38,'sub':18} and r['gate_counts']==counts and r['live_gates']==86 and r['residual_gates']==77
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-87gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
