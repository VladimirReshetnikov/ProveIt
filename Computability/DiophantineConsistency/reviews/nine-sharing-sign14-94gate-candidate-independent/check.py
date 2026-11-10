#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-94gate-candidate';old=root/'research/nine-sharing-sign14-95gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='b00a2d0c4d0c3a25dc7c8fdd2e41690bdaab0315b4f9c4586e9e067c577f1439'
assert sha(p/'seed.json')=='ea47ff1c96d90b3d66d26937a948706149bea8602aa88166dba33b27b59d3c3c' and sha(p/'build.py')=='814fe981afaf71235c6de8c6215aa53bf679b96c0a84ae69a6031e22d19c0e9d' and sha(p/'result.json')=='11fd1e3bc2c1e4bca57bc93373d0ddab1b72d4c22ea248ca1caf66c42af61efe'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));q=a(b,n(1));horiz=m(a(v(9),n(1)),q);y=m(a(v(8),n(1)),m(m(q,q),q));aa=a(m(horiz,y),y);c=a(m(a(a(v(11),n(1)),a(v(12),n(1))),y),a(v(11),n(1)));ac=m(aa,c);guard=m(a(v(14),n(1)),a(m(n(4),aa),n(3)));h=a(a(horiz,ac),guard);t=a(a(s(horiz,n(1)),ac),guard);src=m(t,a(t,n(2)));dst=s(m(h,h),n(1));hits=[0]
def change(x):
 if x==src:hits[0]+=1;return dst
 if x[0] in ('add','sub','mul'):return (x[0],change(x[1]),change(x[2]))
 return x
roots=[change(tup(row['expr'])) for row in before['residuals']];assert hits[0]==5==r['identity_occurrences'];assert len(roots)==5==len(after['residuals']) and all(tup(row['expr'])==roots[i] and row['gate']==before['residuals'][i]['gate'] for i,row in enumerate(after['residuals']))
# Independently normalize the structural t=h-1 relation and the ring identity.
def add(x,y,sgn=1):
 z=x.copy()
 for k,val in y.items():z[k]=z.get(k,0)+sgn*val
 return {k:val for k,val in z.items() if val}
def mul(x,y):
 z={}
 for k,val in x.items():
  for l,w in y.items():key=tuple(sorted(k+l));z[key]=z.get(key,0)+val*w
 return {k:val for k,val in z.items() if val}
one={():1};H={(('H',)):1};A={(('A',)):1};G={(('G',)):1};tp=add(add(add(H,one,-1),A),G);hp=add(add(H,A),G);assert tp==add(hp,one,-1);assert mul(tp,add(tp,{():2}))==add(mul(hp,hp),one,-1)
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==85 and len(live)==94 and counts=={'add':37,'mul':40,'sub':17} and r['gate_counts']==counts and r['live_gates']==94 and r['residual_gates']==85
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-95gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
