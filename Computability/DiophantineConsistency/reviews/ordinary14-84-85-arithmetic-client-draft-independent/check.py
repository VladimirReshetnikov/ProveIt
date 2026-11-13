#!/usr/bin/env python3
"""Independent composition and dependency review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-85-arithmetic-client-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
src=pin(A/'ArithmeticComparison.lean','1acd53997ee3c002b8cee4735dcfef2db2a336832819e32033f3abde37f60f64').decode()
pin(A/'check_source.py','e25c345fd8ecbe13e0e42c5dd47febc1b0a265de4b25f5edf8f0e91db9d6be66')
receipt=pin(A/'observation.json','b42acf7bf219919e59e8f6fbd3c573dfb44099ec39540327243a92d8a13b9b65')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-arithmetic-client-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='62a872605ef164da474f51d971848acedb51e5ad5cd4896889d7842b7213c865'
for path,h in {
 'ordinary14-84-85-conditional-model-draft/ConditionalComparison.lean':'204cf248239f6a070176c407f1d8d2ddb8506afad9784e79ac5ab0a0d2638790',
 'ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean':'d16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e',
 'ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean':'5d8dc10ca61726a6c2b939c2d98a784fb06b702348b15fa657badf7545984d3a',
}.items(): pin(D/'research'/path,h)
for f in ('(hU : 0<U) (hY : 0<Y) (hq : 1≤q beta v)',
 '(hX : X=q beta v*v 6) (ha : a=X*Y+Y) (hH : H=4*a+3)',
 '(hR : 3≤R) (hc : c=ycoord R a) (hd : d=xcoord R a)',
 '(hk : k=R+1+U*W)',
 '(hbal : U*d+H*k=U*(X+a*c)+H*(U*v 12+R+1))',
 'gamma_gt_from_modified_balance U H d X Y a c (v 12) k R W (q beta v) (v 6)\n      hU hY hq hX ha hH hR hc hd hk hbal',
 'map_84_to_85 p beta v hport hv hgamma hz',
 '(ht : 4≤t) (hq : q beta v=(Exp.exp t-1)*v 0+1)',
 '(hX : v 6=Exp.exp R) (hdiv : q beta v∣3*v 6)',
 'mersenne_divides_X t R (q beta v) (v 0) (v 6) ht hq hX hdiv',
 'map_85_to_84 p beta v hport hv hd hz'):
 assert f in src,f
def replay(script,result):
 run=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not run.stderr and run.stdout==result
replay(A/'check_source.py',receipt)
for name in ('ordinary14-84-85-conditional-model-draft-independent',
             'ordinary14-modified-carrier-model-facts-draft-independent',
             'ordinary14-modified-carrier-gamma-model-draft-independent'):
 p=D/'reviews'/name; replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source interface and receipt review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_dependency_reviews':3},sort_keys=True,indent=2))
