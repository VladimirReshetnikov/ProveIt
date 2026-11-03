#!/usr/bin/env python3
"""Check q^3 witness substitution, live gate count and exact algebra samples."""
from pathlib import Path
from hashlib import sha256
import json
import random
import sys
if sys.flags.optimize:
    raise SystemExit('Optimized Python is not accepted')
here=Path(__file__).resolve().parent
parent=here.parent/'ordinary12-sum-of-squares-candidate/candidate.json'
oldraw=parent.read_bytes()
if sha256(oldraw).hexdigest() != 'dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee':
    raise RuntimeError('parent graph hash mismatch')
old=json.loads(oldraw); new=json.loads((here/'candidate.json').read_bytes())
def insist(x, why):
    if not x: raise ValueError(why)
expected=[]
for n,op,a,b in old['source']:
    if n=='U': expected.append(['Y','*','q3','s'])
    if n in ('M','folded_q3Bt','g34'): continue
    if n=='g32': op,a,b='+','folded_g31','s'
    if n=='g33': op,a,b='*','qm','g32'
    if n=='Z': a,b='g33','Bt'
    if n=='g39': a=b='qm'
    expected.append([n,op,a,b])
insist(new['source']==expected,'unexpected source graph')
insist(new['witnesses']==[('s' if x=='Y' else x) for x in old['witnesses']],'wrong witness mapping')
insist(new['fixed_numerals']==old['fixed_numerals'],'wrong ports')
rows=new['source']; witness=new['witnesses']; fixed=new['fixed_numerals']
known=set(witness+fixed)|{0,1,2,3,4}; nodes={}
for n,op,a,b in rows:
    insist(n not in known and a in known and b in known and op in ('+','-','*'),'invalid DAG row')
    known.add(n);nodes[n]=(a,b)
live=set(); todo=[new['output']]
while todo:
    x=todo.pop()
    if x in nodes and x not in live:
        live.add(x);todo.extend(nodes[x])
insist(len(rows)==len(live)==92,'wrong live operation count')
insist(all(w in {a for row in rows for a in row[2:]} for w in witness),'unused witness')
counts={op:sum(r[1]==op for r in rows) for op in ['*','+','-']}
insist(counts==new['operation_breakdown']=={'*':51,'+':24,'-':17},'wrong operation counts')
def evaluate(rows, env):
    e=env.copy();e.update({i:i for i in range(5)})
    for n,op,a,b in rows:
        x,y=e[a],e[b]
        e[n]={'*':lambda:x*y,'+':lambda:x+y,'-':lambda:x-y}[op]()
    return e
rng=random.Random(9201)
for _ in range(25):
    env={k:rng.randrange(1,4) for k in witness}
    env.update({k:rng.randrange(0,3) for k in fixed});env['beta']=rng.randrange(1,4)
    r=evaluate(rows,env)
    oldenv={k:env[k] for k in old['witnesses'] if k!='Y'}
    oldenv.update({k:env[k] for k in fixed});oldenv['Y']=r['q3']*env['s']
    q=evaluate(old['source'],oldenv)
    insist(q['Z']==r['q3']*r['Z'],'scaled root identity failed')
    insist(q['A0']==r['q3']**2*r['A0'],'scaled first residual failed')
    insist(q['A1']==r['A1'] and q['N']==r['N'],'later residual mismatch')
    insist((r['P12']==0)==(q['P12']==0),'sample zero equivalence failed')
print(json.dumps({'status':'PASS','candidate_sha256':sha256((here/'candidate.json').read_bytes()).hexdigest(),
  'parent_sha256':sha256(oldraw).hexdigest(),'rows':len(rows),'live':len(live),
  'breakdown':counts,'exact_integer_samples':25},indent=2))
