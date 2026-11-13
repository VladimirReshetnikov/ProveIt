#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-92gate-candidate';old=root/'research/nine-sharing-sign14-93gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(old)=='19d61af5f17e45f1539ac0db733f37821608d7cba6366fd1af19ef94445ad3c1'
assert sha(p/'seed.json')=='968ae6874f126e4f597797acfa486826c221ddd3ed4b1ad0aa2128de0aa61fec' and sha(p/'build.py')=='541d04493c4c3c09538926dc2289a47a37ad86ef5ba3b1a92d63ecfc230ad8fe' and sha(p/'result.json')=='6993fd994b3561120b51095660ad537d79027df393fe562b6e1fd179c09ba85e'
before=json.loads(old.read_text());after=json.loads((p/'seed.json').read_text());r=json.loads((p/'result.json').read_text());assert r['candidate_sha256']==sha(p/'seed.json') and r['source_sha256']==sha(old)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
b=m(port('beta'),a(v(1),n(1)));q=a(b,n(1));h=a(port('K0'),a(v(9),n(1)));d=a(v(2),n(1));g=a(v(3),n(1));c=a(d,g);z=m(a(v(4),n(1)),b);x=m(h,s(q,c));src=s(s(a(x,b),d),z);dst=s(a(x,s(b,d)),z);hits=[0]
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
X={('X',):1};B={('B',):1};D={('D',):1};Z={('Z',):1};assert add(add(add(X,B),D,-1),Z,-1)==add(add(X,add(B,D,-1)),Z,-1)
# Confirm the shared b-d difference was already present in a different residual.
def contains(t,target):return t==target or (t[0] in ('add','sub','mul') and (contains(t[1],target) or contains(t[2],target)))
assert before['residuals'][2]['gate']=='Nt' and tup(before['residuals'][2]['expr'])==src and any(contains(tup(row['expr']),s(b,d)) for i,row in enumerate(before['residuals']) if i!=2)
def gather(x,out):
 if x[0] in ('add','sub','mul'):out.add(x);gather(x[1],out);gather(x[2],out)
base=set()
for x in roots:gather(x,base)
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==83 and len(live)==92 and counts=={'add':37,'mul':39,'sub':16} and r['gate_counts']==counts and r['live_gates']==92 and r['residual_gates']==83
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-93gate-candidate-independent/check.py')],check=True,capture_output=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'external exact ring rewrite and ordered-subtree circuit; no Lean equivalence, minimum, JSON/PDF or file theorem'},indent=2))
