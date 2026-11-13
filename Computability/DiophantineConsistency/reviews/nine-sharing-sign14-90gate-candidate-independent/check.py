#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-90gate-candidate';old=root/'research/nine-sharing-sign14-92gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='968ae6874f126e4f597797acfa486826c221ddd3ed4b1ad0aa2128de0aa61fec'
assert sha(p/'seed.json')=='8d42e6e9dfbbf47431ef25963965174f4746de4104a92db569a57d933d4c50c3' and sha(p/'build.py')=='ca552385b4dab4d03c91936c29507370c57ff1782d1323251d5a8590711cd892' and sha(p/'result.json')=='84cd2227e793e870760b7014396327177ed478ca2c11a16b6506bf4f2ab28692'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));q=a(b,n(1));d=a(v(2),n(1));g=a(v(3),n(1));q2=m(q,q);q3=m(q2,q);rank=a(m(b,s(b,v(2))),g);src=a(m(s(b,d),q3),m(a(d,g),q2));dst=m(rank,q2);hits=[0]
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
one={():1};B={('B',):1};I={('I',):1};G={('G',):1};Q=add(B,one);D=add(I,one);Q2=mul(Q,Q);Q3=mul(Q2,Q);assert add(mul(add(B,D,-1),Q3),mul(add(D,G),Q2))==mul(add(mul(B,add(B,I,-1)),G),Q2)
# Rank factor is already a proper subtree elsewhere in the original residuals.
def contains(t,target):return t==target or (t[0] in ('add','sub','mul') and (contains(t[1],target) or contains(t[2],target)))
assert any(contains(tup(row['expr']),rank) for row in before['residuals'])
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==81 and len(live)==90 and counts=={'add':36,'mul':38,'sub':16} and r['gate_counts']==counts and r['live_gates']==90 and r['residual_gates']==81
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-92gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
