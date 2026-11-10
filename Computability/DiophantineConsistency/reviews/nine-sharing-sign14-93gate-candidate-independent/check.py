#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-93gate-candidate';old=root/'research/nine-sharing-sign14-94gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='ea47ff1c96d90b3d66d26937a948706149bea8602aa88166dba33b27b59d3c3c'
assert sha(p/'seed.json')=='19d61af5f17e45f1539ac0db733f37821608d7cba6366fd1af19ef94445ad3c1' and sha(p/'build.py')=='c9361a025e1c293f6d9d356940465adf7887ff9f73cc307ab45834f0db221e10' and sha(p/'result.json')=='5b2d81fc1ca90a90704a8231c1ba0ab78256675abe352a28b6d0a3402a33d5e9'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));q=a(b,n(1));g=a(v(3),n(1));src=s(a(m(b,q),g),m(b,a(v(2),n(1))));dst=a(m(b,s(b,v(2))),g);hits=[0]
def change(x):
 if x==src:hits[0]+=1;return dst
 if x[0] in ('add','sub','mul'):return (x[0],change(x[1]),change(x[2]))
 return x
roots=[change(tup(row['expr'])) for row in before['residuals']];assert hits[0]==4==r['identity_occurrences'];assert len(roots)==5==len(after['residuals']) and all(tup(row['expr'])==roots[i] and row['gate']==before['residuals'][i]['gate'] for i,row in enumerate(after['residuals']))
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
one={():1};B={('B',):1};I={('I',):1};G={('G',):1};assert add(add(mul(B,add(B,one)),G),mul(B,add(I,one)),-1)==add(mul(B,add(B,I,-1)),G)
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==84 and len(live)==93 and counts=={'add':37,'mul':39,'sub':17} and r['gate_counts']==counts and r['live_gates']==93 and r['residual_gates']==84
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-94gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
