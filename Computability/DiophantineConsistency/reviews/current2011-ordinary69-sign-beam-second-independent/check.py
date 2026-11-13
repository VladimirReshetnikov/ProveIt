#!/usr/bin/env python3
import hashlib, itertools, json, subprocess, sys
from collections import Counter, defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
base=Path(__file__).resolve().parents[2]; repo=base.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
p=base/'research/current2011-ordinary69-sign-beam'
for name,digest in {'README.md':'6a8837cab6ff5e7743be0de3db576a00e1a50c37b113859191de668bc39eeff0','search.py':'625955a4b06ead26659e75571bbb343bb1637701629b7a72380c6eb6a27c9e30','result.json':'fd2a234bc1f3d9fcb44cc319f69282c166d56ad8eca25e734c20d92a709042c2'}.items(): assert sha(p/name)==digest
G=base/'research/current2011-ordinary69-84-candidate/polynomial.json';E=base/'research/nine-sharing-sign14-positive74-structural-search/search_canonical.py'
assert sha(G)=='c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a'
assert sha(E)=='5f683e6e9b3cc46450e4edcc566610862730b8e58ab574a4e12496dc67b71bb6'
for f,h in [('reviews/current2011-ordinary69-84-candidate-independent/check.py','23868d9e477c4038a67402a56c9378d4fca6ad020094672ae32d2e6c782edba8'),('reviews/nine-sharing-sign14-positive74-structural-search-independent/check.py','5b14ceba683062f87931a078e3218e19a82c8e68e2c94d862e3dc0efc91a9953')]:
 q=base/f;assert sha(q)==h
 subprocess.run([sys.executable,'-I','-S','-B',str(q)],cwd=repo,capture_output=True,check=True,timeout=180)
g=json.loads(G.read_text()); names={r[0] for r in g['source']}; leaves=set(g['witnesses']+g['fixed_numerals']); assert len(names)==69 and len(leaves)==18
seen=set(); uses=defaultdict(list); forms={}; unique={}
def arg(x):
 if type(x)==int:return ('int',x)
 assert type(x)==str and (x in seen or x in leaves)
 return forms[x] if x in seen else ('leaf',x)
for name,op,a,b in g['source']:
 assert name not in seen and op in ('+','-','*')
 for x in (a,b):
  if isinstance(x,str): uses[x].append(name)
 aa,bb=arg(a),arg(b)
 if op in ('+','*') and repr(aa)>repr(bb):aa,bb=bb,aa
 form=(op,aa,bb); forms[name]=form; unique.setdefault(form,[]).append(name);seen.add(name)
for name in ('N0','N1','Nt'):
 assert forms[name][0]=='-' and unique[forms[name]]==[name]
assert uses['N0']==['PQ'] and uses['N1']==['PQ'] and uses['Nt']==['PQW']
rows={r[0]:r for r in g['source']}
assert rows['PQ']==['PQ','*','N0','N1'] and rows['PQW']==['PQW','*','PQ','Nt']
# Exact formal coefficients of X(X-2), independent of the search's sparse-polynomial implementation.
# X is a*b*c and a pair of sign reversals changes its multiplier by +1.
basepoly={(2,2,2):1,(1,1,1):-2}
for i,j in itertools.combinations(range(3),2):
 signs=[-1 if k in (i,j) else 1 for k in range(3)]; multiplier=signs[0]*signs[1]*signs[2]
 assert {(2,2,2):multiplier**2,(1,1,1):-2*multiplier}==basepoly
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'search.py')],cwd=repo,capture_output=True,check=True,timeout=360)
assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
x=json.loads(r.stdout);assert x['status']=='PASS_BOUNDED_SEARCH' and x['best_observed']==69 and len(x['depths'])==10 and all(d['best']==69 and d['beam']==160 for d in x['depths'])
assert x['original_count']==69 and set(x['sign_variants'].values())=={69} and x['intermediate_gate_limit']==71
print(json.dumps({'status':'PASS_INDEPENDENT_BOUNDED_AUDIT','receipt_reproduced':True,'sign_pairs':3,'rewrites_independently_checked':1056,'depths':10,'best_observed':69,'scope':'Bounded visited beam only; no global minimum, new Lean proof, or external-file binding.'},indent=2))
