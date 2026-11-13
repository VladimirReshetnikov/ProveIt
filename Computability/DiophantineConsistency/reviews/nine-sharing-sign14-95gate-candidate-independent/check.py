#!/usr/bin/env python3
import collections,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-95gate-candidate';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'build.py')=='5f76114028429d9a8a7bc533b6e023a1b80c480e30e66a53cb5b4c42f0d8afa6' and sha(p/'seed.json')=='b00a2d0c4d0c3a25dc7c8fdd2e41690bdaab0315b4f9c4586e9e067c577f1439' and sha(p/'result.json')=='83ea45f32e0fc0f97cac3ac7005ecadf9ca74ff7cfb9913942cda772bcc1add9'
source=root/'research/nine-sharing-sign14-tau-candidate/seed.json';assert sha(source)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';before=json.loads(source.read_text());after=json.loads((p/'seed.json').read_text());rec=json.loads((p/'result.json').read_text());assert rec['candidate_sha256']==sha(p/'seed.json') and rec['source_sha256']==sha(source)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
a=lambda x,y:('add',x,y);sub=lambda x,y:('sub',x,y);mul=lambda x,y:('mul',x,y);num=lambda n:('num',n);var=lambda i:('var',i);port=lambda x:('port',x)
b=mul(port('beta'),a(var(1),num(1)));q=a(b,num(1));w=var(9);wp=a(w,num(1));old=a(mul(w,q),b);new=sub(mul(wp,q),num(1));hits=[0]
def transform(e):
 if e==old:hits[0]+=1;return new
 if e[0] in ('add','sub','mul'):return (e[0],transform(e[1]),transform(e[2]))
 return e
roots=[transform(tup(r['expr'])) for r in before['residuals']];assert hits[0]==10==rec['identity_1_occurrences']
a0=a(port('K0'),wp);d=a(var(2),num(1));c=a(d,a(var(3),num(1)));z=mul(a(var(4),num(1)),b)
oldnt=sub(sub(a(mul(a0,q),q),a(a(mul(a0,c),d),z)),num(1));newnt=sub(sub(a(mul(a0,sub(q,c)),b),d),z);assert before['residuals'][2]['gate']=='Nt' and roots[2]==oldnt
roots[2]=newnt;assert all(tup(r['expr'])==roots[i] for i,r in enumerate(after['residuals'])) and all(before['residuals'][i]['gate']==after['residuals'][i]['gate'] for i in range(5))
# Independent sparse monomial normalization for the two schematic identities.
def plus(x,y,sgn=1):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def prod(x,y):
 z={}
 for a0,x0 in x.items():
  for b0,y0 in y.items():k=tuple(sorted(a0+b0));z[k]=z.get(k,0)+x0*y0
 return {k:v for k,v in z.items() if v}
one={():1};sym=lambda n:{(n,):1};B,W,A,C,D,Z=map(sym,'BWACDZ');Q=plus(B,one)
assert plus(prod(W,Q),B)==plus(prod(plus(W,one),Q),one,-1)
assert plus(plus(plus(prod(A,Q),Q),plus(plus(prod(A,C),D),Z),-1),one,-1)==plus(plus(plus(prod(A,plus(Q,C,-1)),B),D,-1),Z,-1)
def gather(t,acc):
 if t[0] in ('add','sub','mul'):acc.add(t);gather(t[1],acc);gather(t[2],acc)
base=set()
for x in roots:gather(x,base)
sq=[mul(x,x) for x in roots];out=sq[0]
for x in sq[1:]:out=a(out,x)
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==86 and len(live)==95 and counts=={'add':38,'mul':40,'sub':17} and rec['gate_counts']==counts and rec['live_gates']==95
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_occurrences':hits[0],'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'exact external ring rewrites and ordered subtree circuit; no Lean equivalence/minimality/file binding'},indent=2))
