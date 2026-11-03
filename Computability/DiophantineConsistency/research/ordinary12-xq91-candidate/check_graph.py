#!/usr/bin/env python3
"""Check live q*W witness graph and the exact transformed-node comparisons."""
from pathlib import Path
from hashlib import sha256
import json,random,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent; parent=H.parent/'ordinary12-qcube92-candidate/candidate.json';raw=parent.read_bytes()
if sha256(raw).hexdigest()!='3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3':raise RuntimeError('parent hash drift')
a=json.loads(raw); b=json.loads((H/'candidate.json').read_bytes())
def need(x,m):
 if not x:raise RuntimeError(m)
expected=[]
for n,op,x,y in a['source']:
 if n in ('g25','g26','g55'):continue
 if n=='g27':expected.append(['kw','+','K0','w']);x,y='C','kw'
 if n=='g28':op,x,y='-','g27','F'
 if n=='Bt':op,x,y='*','q','g28'
 if n=='g54':op,x,y='+','gamma','w'
 if n=='g56':op,x,y='*','U','g54'
 expected.append([n,op,x,y])
 if n=='q':expected.append(['X','*','q','w'])
need(b['source']==expected,'graph transformation mismatch')
need(b['witnesses']==[('w' if x=='X' else x) for x in a['witnesses']],'witness mapping')
need(b['fixed_numerals']==a['fixed_numerals'] and b['output']==a['output'],'port or output mapping')
rows=b['source'];known=set(b['witnesses']+b['fixed_numerals'])|{0,1,2,3,4};parents={}
for n,op,x,y in rows:
 need(n not in known and x in known and y in known and op in ('+','-','*'),'bad graph topology')
 known.add(n);parents[n]=(x,y)
live=set();todo=[b['output']]
while todo:
 n=todo.pop()
 if n in parents and n not in live:live.add(n);todo.extend(parents[n])
need(len(rows)==len(live)==91,'wrong live count')
counts={op:sum(x[1]==op for x in rows) for op in ['*','+','-']}
need(counts==b['operation_breakdown']=={'*':50,'+':24,'-':17},'operation breakdown')
def evaluate(rows,env):
 v=env.copy();v.update({i:i for i in range(5)})
 for n,op,x,y in rows:
  X,Y=v[x],v[y];v[n]={'*':lambda:X*Y,'+':lambda:X+Y,'-':lambda:X-Y}[op]()
 return v
rng=random.Random(9101)
for _ in range(30):
 env={k:rng.randrange(1,4) for k in b['witnesses']};env.update({k:rng.randrange(0,4) for k in b['fixed_numerals']});env['beta']=rng.randrange(1,4)
 new=evaluate(rows,env); oldenv={k:env[k] for k in a['witnesses'] if k!='X'};oldenv.update({k:env[k] for k in a['fixed_numerals']});oldenv['X']=new['q']*env['w'];old=evaluate(a['source'],oldenv)
 for name in ('X','Y','U','E','Bt','g56','A0','A1','N','P12'):
  need(old[name]==new[name],'node identity failed '+name)
print(json.dumps({'status':'PASS','candidate_sha256':sha256((H/'candidate.json').read_bytes()).hexdigest(),'parent_sha256':sha256(raw).hexdigest(),'rows':len(rows),'live':len(live),'breakdown':counts,'exact_integer_samples':30},indent=2))
