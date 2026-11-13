#!/usr/bin/env python3
"""Source-pinned graph transform, exact-degree audit, and witness-map controls."""
import gzip,hashlib,json,random
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
PARENT=ROOT/'research/adaptive87-four-square-current88-30/graph.json';CHILD=HERE/'graph.json';PORTS=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PINS={PARENT:'293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed',CHILD:'456d214dbda2354b90bba3d1e883ef73dd66b8eec66bd8860b261f807c15d126',PORTS:'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in PINS.items():assert sha(p)==h
old=json.loads(PARENT.read_bytes());g=json.loads(CHILD.read_bytes())
assert g['source_parent_sha256']==sha(PARENT)
assert g['witnesses']==['auxPositive' if n=='u' else n for n in old['witnesses']]
assert g['fixed_numerals']==old['fixed_numerals'] and g['output']==old['output']
assert sum(r[0]=='g78' and r==['g78','+','V','u'] for r in old['source'])==1
assert sum(r==['y2','*','g78','g78'] for r in old['source'])==1
expected=[(['y2','*','auxPositive','auxPositive'] if r[0]=='y2' else r) for r in old['source'] if r[0]!='g78']
assert g['source']==expected
known=set(g['witnesses']+g['fixed_numerals']);rows={}
for n,op,a,b in g['source']:
 assert n not in known and op in ('+','-','*') and all(not isinstance(v,str) or v in known for v in (a,b))
 known.add(n);rows[n]=(op,a,b)
need={g['output']}
for n,op,a,b in reversed(g['source']):
 if n in need:need.update(z for z in (a,b) if isinstance(z,str))
assert set(rows)<=need and set(g['witnesses']+g['fixed_numerals'])<=need and len(rows)==87
meta=json.loads(PORTS.read_bytes())['coefficient_binding']['ports'];port_mod={};prime=1000000007
for n,m in meta.items():
 packed=(PORTS.parent/'coefficients'/m['file']).read_bytes();raw=gzip.decompress(packed)
 assert hashlib.sha256(packed).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes']
 if n=='beta':assert any(raw), 'beta must be a positive encoded natural'
 port_mod[n]=int.from_bytes(raw,'big')%prime

def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
def plus(x,y,s):return trim([((x[k] if k<len(x) else 0)+s*(y[k] if k<len(y) else 0))%prime for k in range(max(len(x),len(y)))])
def mul(x,y):
 z=[0]*(len(x)+len(y)-1)
 for j,a in enumerate(x):
  for k,b in enumerate(y):z[j+k]=(z[j+k]+a*b)%prime
 return trim(z)
poly={**{n:[v] for n,v in port_mod.items()},**{n:[0,1] for n in g['witnesses']}}
deg={**{n:0 for n in g['fixed_numerals']},**{n:1 for n in g['witnesses']}}
for n,op,a,b in g['source']:
 va=poly[a] if isinstance(a,str) else [a%prime];vb=poly[b] if isinstance(b,str) else [b%prime]
 poly[n]=mul(va,vb) if op=='*' else plus(va,vb,1 if op=='+' else -1)
 da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
 deg[n]=da+db if op=='*' else max(da,db)
assert deg['output']==36 and len(poly['output'])-1==36 and poly['output'][-1]==57192905

def evaluate(graph,v):
 vals=dict(v)
 for n,op,a,b in graph['source']:
  x=vals[a] if isinstance(a,str) else a;y=vals[b] if isinstance(b,str) else b
  vals[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return vals
# These check only the syntactic witness substitutions; they are not zero proofs.
rng=random.Random(17036);controls={'absolute_value':0,'positive_difference':0}
for _ in range(40):
 common={n:rng.randrange(1,4) for n in old['witnesses']};common.update({n:rng.randrange(0,4) for n in old['fixed_numerals']})
 p=evaluate(old,common);child={n:(abs(p['g78']) if n=='auxPositive' else common[n]) for n in g['witnesses']};child.update({n:common[n] for n in g['fixed_numerals']});c=evaluate(g,child)
 assert c['output']==p['output'];controls['absolute_value']+=1
 # Independent positive child ordinate larger than V gives a legal parent difference.
 child['auxPositive']=max(1,c['V']+1);c=evaluate(g,child)
 parent={n:(child['auxPositive']-c['V'] if n=='u' else child[n]) for n in old['witnesses']};parent.update({n:common[n] for n in old['fixed_numerals']})
 assert parent['u']>0 and evaluate(old,parent)['output']==c['output'];controls['positive_difference']+=1
print(json.dumps({'status':'PASS','parent_sha256':sha(PARENT),'child_sha256':sha(CHILD),'live_rows':len(rows),
 'operation_counts':{op:sum(r[1]==op for r in g['source']) for op in ('*','+','-')},'degree_syntactic_upper':deg['output'],
 'current_port_diagonal_degree':len(poly['output'])-1,'leading_coefficient_mod_prime':poly['output'][-1],
 'prime':prime,'beta_encoded_natural_positive':True,'map_controls':controls,
 'limits':['Proof of zero equivalence is mathematical in README, not inferred from controls.',
 'Only standard positive integers; no Lean elaboration, all-model bridge or iPRA claim.',
 'Other ports may be arbitrary integers; beta>=0 suffices for the stated witness argument.']},indent=2,sort_keys=True))
