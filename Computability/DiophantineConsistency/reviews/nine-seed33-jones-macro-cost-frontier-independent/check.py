#!/usr/bin/env python3
import collections,hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed33-jones-macro-cost-survey';recipe=d/'research/nine-seed33-jones-compact-macro-prototype/recipe.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'check.py')=='7568cb93ec02e890503ce1f40103b43b493d0f3e93a08389647e8461150d2e06' and sha(p/'result.json')=='3263084bb0db85043b0c338c41647228bbc9f1915c0fe82840c559261c99dbd7' and sha(recipe)=='06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,check=True,timeout=30);assert not r.stderr and r.stdout.encode()==(p/'result.json').read_bytes();o=json.loads(r.stdout);nodes=json.loads(recipe.read_text())['nodes'];assert len(nodes)==45
# Independent iterative typed traversal; exponent/bound ASTs counted as
# metadata, never as ring operations. Each syntactic node visited once.
counts={'ring':collections.Counter(),'nat':collections.Counter()};todo=[('ring',n['expr']) for n in nodes]
while todo:
 kind,t=todo.pop();assert isinstance(t,list) and t;op=t[0];counts[kind][op]+=1
 if kind=='nat':
  if op in ('lit','index','expo'):assert len(t)==2
  else:assert op in ('add','sub','mul','pow') and len(t)==3;todo.extend([('nat',t[1]),('nat',t[2])])
 else:
  if op in ('const','var','ref','fixed','pcoef'):assert len(t)==2
  elif op in ('add','sub','mul'):assert len(t)==3;todo.extend([('ring',t[1]),('ring',t[2])])
  elif op=='pow':assert len(t)==3;todo.extend([('ring',t[1]),('nat',t[2])])
  elif op=='sum_range':assert len(t)==4;todo.extend([('nat',t[2]),('ring',t[3])])
  elif op=='sum_star':assert len(t)==3;todo.append(('ring',t[2]))
  else:raise AssertionError(op)
ops=('add','sub','mul','pow','sum_range','sum_star');leaves=('const','var','ref','fixed','pcoef')
assert {k:counts['ring'][k] for k in ops}==o['ring_operator_counts']=={'add':39,'sub':23,'mul':64,'pow':44,'sum_range':2,'sum_star':1}
assert sum(counts['ring'][k] for k in ops)==o['total_unit_macro_operators']==173
assert {k:counts['ring'][k] for k in leaves}==o['ring_leaf_occurrences'] and dict(counts['nat'])==o['natural_metadata_counts']
print(json.dumps({'status':'PASS_SERIALIZED_UNIT_MACRO_COUNT','recipe_sha256':sha(recipe),'ring_counts':o['ring_operator_counts'],'total':173,'scope':'External serialized macro convention only; no binary circuit count, expansion, evaluation cost or Lean JSON binding'},indent=2,sort_keys=True))
