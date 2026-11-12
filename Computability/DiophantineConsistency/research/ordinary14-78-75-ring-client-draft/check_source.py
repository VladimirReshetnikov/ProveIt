#!/usr/bin/env python3
from pathlib import Path
from functools import lru_cache
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
s=(P/'Ring78To75.lean').read_text()
for t in ('theorem common_fields','theorem first_eval','theorem factor_evals','[CommRing R]','(P75NegativePell.graph p).aux=(P78AuxRoot.graph p).aux'):
 assert t in s,t
files=[D/'research/ordinary14-aux-root78/candidate.json',D/'research/ordinary14-negative-pell75/candidate.json'];a,b=[json.loads(p.read_bytes()) for p in files]
assert len(a['source'])==78 and len(b['source'])==75 and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
def dag(g):return {n:(op,x,y) for n,op,x,y in g['source']}
x,y=map(dag,(a,b))
def expr(rows,name):
 @lru_cache(None)
 def walk(k):
  if not isinstance(k,str):return ('const',k)
  if k not in rows:return ('var',k)
  op,u,v=rows[k];return (op,walk(u),walk(v))
 return walk(name)
for old,new in [('A1','A1'),('Fa','Fa'),('g72','g72'),('guard','guard'),('g38','g38'),('g40','g40')]:assert expr(x,old)==expr(y,new),(old,new)
assert x['g41']==('+',1,'g40') and x['A0']==('-','g38','g41') and y['F0']==('-','g38','g40')
assert y['F1']==('+',1,'A1') and y['Fs']==('+',1,'g72') and y['Fg']==('+',1,'guard')
def calc(g,values):
 v=dict(values)
 for n,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(7875)
for _ in range(500):
 v={name:rng.randrange(-6,7) for name in a['witnesses']+a['fixed_numerals']};p=calc(a,v);q=calc(b,v)
 assert (q['F0'],q['F1'],q['Fa'],q['Fs'],q['Fg'])==(1+p['A0'],1+p['A1'],p['Fa'],1+p['g72'],1+p['guard'])
for directory in ('ordinary14-aux-root78-lean-draft','ordinary14-unit75-guard74-lean-draft'):
 p=D/'research'/directory
 result=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
 assert result.stdout==(p/'observation.json').read_bytes() and not result.stderr
paths=[P/'Ring78To75.lean',D/'research/ordinary14-aux-root78-lean-draft/P78AuxRoot.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P75NegativePell.lean']+files
print(json.dumps({'scope':'source/DAG and signed finite controls; no Lean or model zero theorem','files':{str(p.relative_to(D)):H(p) for p in paths},'signed_controls':500,'generator_receipts_replayed':2},sort_keys=True,indent=2))
