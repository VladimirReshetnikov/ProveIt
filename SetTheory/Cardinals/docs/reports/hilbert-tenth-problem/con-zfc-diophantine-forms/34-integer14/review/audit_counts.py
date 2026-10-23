"""Owned read-only structural audit; no imported code is executed."""
import json,hashlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
if not __debug__: raise RuntimeError('Run without optimization')
ledger=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
for rec in ledger['files']:
 p=ROOT/rec['path'].split('con-zfc-diophantine-forms/')[1];d=p.read_bytes()
 sha=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha(d)==rec['sha'],str(p)
results=[]
for p in sorted(ROOT.rglob('*.json')):
 if p.name=="COUNT_AUDIT.json":continue
 j=json.loads(p.read_text())
 if not isinstance(j,dict):continue
 if 'source' in j and isinstance(j['source'],list):
  src=j['source'];env=set(j['witnesses']+j['fixed_numerals']);parents={};ops={}
  for name,op,a,b in src:
   assert name not in env and op in '+-*'
   assert all(isinstance(x,int) or x in env for x in (a,b))
   env.add(name);parents[name]=[x for x in (a,b) if isinstance(x,str)];ops[name]=op
  live=set();todo=[j['output']]
  while todo:
   n=todo.pop()
   if n in live:continue
   live.add(n);todo+=parents.get(n,[])
  assert set(j['witnesses'])<=live
  cnt=Counter(ops[n] for n in live if n in ops)
  results.append({'path':str(p.relative_to(ROOT)),'variables':len(j['witnesses']),'gates':sum(cnt.values()),'operations':dict(sorted(cnt.items())),'dead_gates':len(src)-sum(cnt.values()),'reported_degree':j.get('exact_degree')})
 elif 'nodes' in j:
  nodes=j['nodes'];live=set();todo=[j['output']]
  while todo:
   i=todo.pop()
   if i in live:continue
   live.add(i);n=nodes[i]
   if n['kind'] in ['add','sub','mul']:
    assert n['left']<i and n['right']<i;todo.extend([n['left'],n['right']])
  cnt=Counter(nodes[i]['kind'] for i in live if nodes[i]['kind'] in ['add','sub','mul'])
  variables=[nodes[i]['name'] for i in live if nodes[i]['kind']=='variable']
  assert set(variables)==set(j['variables'])
  results.append({'path':str(p.relative_to(ROOT)),'variables':len(variables),'gates':sum(cnt.values()),'operations':dict(sorted(cnt.items())),'reported_degree':j.get('exact_degree_formula',j.get('exact_degree'))})
print(json.dumps({'source_files':len(ledger['files']),'counts':results},indent=2))
