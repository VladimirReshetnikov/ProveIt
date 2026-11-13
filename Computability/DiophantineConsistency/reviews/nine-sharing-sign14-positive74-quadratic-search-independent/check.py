#!/usr/bin/env python3
import hashlib,itertools,json,math,subprocess,sys
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-quadratic-search';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();manifest=json.loads((p/'manifest.json').read_text());assert all(sha(p/n)==h for n,h in manifest['sha256'].items())
# Independently expand the discriminant identity in Z[a,b,c,r,s].
def add(x,y,k=1):
 z=defaultdict(int,x)
 for m,v in y.items():z[m]+=k*v
 return {m:v for m,v in z.items() if v}
def mul(x,y):
 z=defaultdict(int)
 for a,u in x.items():
  for b,v in y.items():z[tuple(i+j for i,j in zip(a,b))]+=u*v
 return {m:v for m,v in z.items() if v}
def scale(x,k):return {m:k*v for m,v in x.items() if k*v}
V=[{tuple(int(i==j) for i in range(5)):1} for j in range(5)];a,b,c,r,s=V;q=add(add(mul(a,mul(r,r)),mul(b,mul(r,s))),mul(c,mul(s,s)));w=add(scale(mul(a,r),2),mul(b,s));disc=add(scale(mul(a,c),4),mul(b,b),-1);assert scale(mul(a,q),4)==add(mul(w,w),mul(disc,mul(s,s)))
forms=[(a,b,c) for a in range(1,4) for c in range(1,4) for b in range(-4,5) if 4*a*c>b*b];assert len(forms)==61 and all(a>0 and c>0 and 4*a*c-b*b>0 for a,b,c in forms)
for a,b,c in forms:
 for x,y in itertools.product(range(-7,8),repeat=2):
  Q=a*x*x+b*x*y+c*y*y;assert Q>=0 and ((Q==0)==(x==0 and y==0))
@lru_cache(None)
def trees(xs):
 if len(xs)==1:return {xs[0]}
 result=set();n=len(xs)
 for mask in range(1,(1<<n)-1):
  if not mask&1:continue
  left=tuple(xs[i] for i in range(n) if mask>>i&1);right=tuple(xs[i] for i in range(n) if not mask>>i&1)
  for a in trees(left):
   for b in trees(right):result.add((a,b))
 return result
assert len(trees((0,1,2,3)))==15 and len(list(itertools.combinations(range(5),2)))==10
P=1000000007;assert P%4==3 and all(P%d for d in range(2,math.isqrt(P)+1));line=(p/'result.txt').read_text().strip();assert line.startswith('SUMMARY ');v=json.loads(line[8:]);st=v['stats'];assert v['script_sha256']==sha(p/'search.py') and v['forms']==61 and v['hits']==0 and v['positive_control_live_before']==76 and v['positive_control_live_after']==74 and v['prime']==P and v['samples']==3 and st=={'pair_form_tests':610,'matching_0':1,'matching_1':23,'matching_2':1492,'candidates_counted':22740} and 15*(1+23+1492)==22740
# The control checks an inserted pair of cancelling gates, the original two-square wire,
# and existing 74-gate root; it is not a separate exhaustive run over a 76-gate graph.
for f in ('nine-sharing-sign14-positive74-structural-search-independent','nine-sharing-sign14-positive74-circuit-output-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],cwd=repo,capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'61 positive-definite forms on ten pairs, bounded modular recipes and 15 sum trees; no exact candidate, global minimum or file theorem'},indent=2))
