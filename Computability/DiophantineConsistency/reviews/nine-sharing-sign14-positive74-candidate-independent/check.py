#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-candidate';src=root/'research/nine-sharing-sign14-86gate-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(src)=='c397c797e39f54bbe4e2a621a15cd94a898a6b44604379aae28a21f0d5861497' and sha(p/'seed.json')=='10d4e4739d5e6657cc43ea71792c363bf0e292fd65f0cf11372fd20b4b5de15b' and sha(p/'build.py')=='26868411d38e5fa77c6fad896b7857dfc4d33e1cdc6889505ed6ebdcda3af4b4' and sha(p/'result.json')=='d5eb45991b589bb8f2e39619f1869c69d9632e7763bc7ca9c71b812e8580e2b2'
before=json.loads(src.read_text());after=json.loads((p/'seed.json').read_text());rec=json.loads((p/'result.json').read_text());assert rec['source_sha256']==sha(src) and rec['candidate_sha256']==sha(p/'seed.json') and after['source_sha256']==sha(src) and after['schema']=='sign14-positive-coordinate-residuals-v1' and '14 strictly positive integer variables u[1..14]' in after['domain'] and 'arbitrary integer ports beta, K0, MC, MF'==after['ports']
a=lambda x,y:('add',x,y);s=lambda x,y:('sub',x,y);m=lambda x,y:('mul',x,y);n=lambda k:('num',k);v=lambda k:('var',k);port=lambda k:('port',k)
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
def substitute(x):
 if x[0]=='var':assert type(x[1]) is int and 1<=x[1]<=14;return s(x,n(1))
 if x[0] in ('add','sub','mul'):return (x[0],substitute(x[1]),substitute(x[2]))
 assert x[0] in ('num','port');return x
B=m(port('beta'),v(1));hits=collections.Counter()
def normalize(x):
 # Work on the uniformly substituted AST and apply exact ring identities top-down.
 if x[0]=='add' and x[1][0]=='sub' and x[1][1][0]=='var' and x[1][2]==n(1) and x[2]==n(1):hits['positive_shift']+=1;return x[1][1]
 if x==s(m(port('beta'),a(s(v(1),n(1)),n(1))),s(v(2),n(1))):hits['q_minus_f']+=1;return s(a(B,n(1)),v(2))
 if x[0]=='sub' and x[1][0]=='sub' and x[1][2]==s(v(2),n(1)) and x[2]==n(1):hits['minus_f']+=1;return s(normalize(x[1][1]),v(2))
 if x[0] in ('add','sub','mul'):return (x[0],normalize(x[1]),normalize(x[2]))
 return x
roots=[normalize(substitute(tup(row['expr']))) for row in before['residuals']];assert hits=={'positive_shift':527,'q_minus_f':9,'minus_f':1}==rec['rewrite_hits'];assert len(roots)==len(after['residuals'])==5 and all(tup(row['expr'])==roots[i] and row['gate']==before['residuals'][i]['gate'] for i,row in enumerate(after['residuals']))
# Exact local identities after substitution, checked by independent sparse algebra.
def add(x,y,k=1):
 z=x.copy()
 for a0,b0 in y.items():z[a0]=z.get(a0,0)+k*b0
 return {a0:b0 for a0,b0 in z.items() if b0}
def mul(x,y):
 z={}
 for a0,b0 in x.items():
  for c0,d0 in y.items():key=tuple(sorted(a0+c0));z[key]=z.get(key,0)+b0*d0
 return {a0:b0 for a0,b0 in z.items() if b0}
O={():1};U={('U',):1};F={('F',):1};B0={('B',):1};A0={('A',):1};assert add(add(U,O,-1),O)==U and add(B0,add(F,O,-1),-1)==add(add(B0,O),F,-1) and add(add(A0,add(F,O,-1),-1),O,-1)==add(A0,F,-1)
# Positive u -> natural v=u-1 and inverse u=v+1 are inverse maps coordinatewise.
for u in range(1,15):assert (u-1)>=0 and (u-1)+1==u
for z in range(15):assert z+1>=1 and (z+1)-1==z
variables=set();ports=set()
def gather(x,acc):
 if x[0] in ('add','sub','mul'):acc.add(x);gather(x[1],acc);gather(x[2],acc)
 elif x[0]=='var':variables.add(x[1])
 elif x[0]=='port':ports.add(x[1])
 else:assert x[0]=='num'
base=set()
for x in roots:gather(x,base)
assert variables==set(range(1,15)) and ports=={'beta','K0','MC','MF'}
out=m(roots[0],roots[0])
for x in roots[1:]:out=a(out,m(x,x))
live=set();gather(out,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(base)==65 and len(live)==74 and counts=={'add':18,'mul':38,'sub':18} and rec['gate_counts']==counts and rec['live_gates']==74 and rec['residual_gates']==65
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-86gate-candidate-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','rewrite_hits':dict(hits),'variables':len(variables),'residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'positive-coordinate ring substitution and exact-sharing circuit; no Lean/minimality/JSON/PDF/file theorem'},indent=2))
