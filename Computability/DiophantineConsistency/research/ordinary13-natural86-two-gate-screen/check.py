#!/usr/bin/env python3
"""Bounded single-consumer two-to-one exact-target rejection screen; no Lean."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
p=D/'research/ordinary13-natural-forced-w86/candidate.json';raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();assert h=='75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50'
g=json.loads(raw);rows=g['source'];assert len(rows)==86 and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
mod=1000000007;rng=random.Random(947521);inputs=g['witnesses']+g['fixed_numerals'];samples=[]
for _ in range(6):
 e={x:rng.randrange(1,mod) for x in inputs}
 for n,o,a,b in rows:
  a=a if type(a) is int else e[a];b=b if type(b) is int else e[b]
  e[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%mod
 samples.append(e)
uses=defaultdict(set)
for n,o,a,b in rows:
 for x in (a,b):
  if isinstance(x,str):uses[x].add(n)
positions={r[0]:i for i,r in enumerate(rows)}
candidates=0;pairs=0;survivors=[];per_op={'+':0,'-':0,'*':0}
def evaluate(op,a,b):return (a*b if op=='*' else a+b if op=='+' else a-b)%mod
for i,(n,_,_,_) in enumerate(rows):
 if len(uses[n])!=1:continue
 final=next(iter(uses[n]));j=positions[final];assert j>i
 # n has no other consumer, so no other earlier node can depend on it.
 avail=inputs+[r[0] for r in rows[:j] if r[0]!=n]+[0,1,2,3,4]
 values={x:tuple((x if type(x) is int else e[x])%mod for e in samples) for x in avail}
 target=tuple(e[final] for e in samples);pairs+=1
 for x in avail:
  for y in avail:
   for op in ('+','-','*'):
    candidates+=1;per_op[op]+=1
    if evaluate(op,values[x][0],values[y][0])!=target[0]:continue
    if all(evaluate(op,values[x][t],values[y][t])==target[t] for t in range(1,len(samples))):survivors.append([n,final,x,op,y])
print(json.dumps({'scope':'all single-consumer predecessor/consumer cuts, replaced by one earlier-wire binary gate; six modular counterexamples reject identities, not zero-set or global lower bounds','graph_sha256':h,'modulus':mod,'rng_seed':947521,'samples':len(samples),'single_consumer_cuts':pairs,'replacement_candidates':candidates,'candidates_by_operation':per_op,'survivors':survivors,'lean_elaboration':False},sort_keys=True,indent=2))
