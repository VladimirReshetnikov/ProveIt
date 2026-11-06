#!/usr/bin/env python3
"""External comparison only; this is not a Lean proof of lift correctness."""
import hashlib,json,re
from pathlib import Path
p=Path(__file__).resolve().parent; d=p.parents[1]
a=d/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
b=d/'research/nine-sharing-quartic65-sign33-candidate/seed.json'
x=json.loads(a.read_text());y=json.loads(b.read_text())
assert x['source_graph_sha256']==y['source_graph_sha256']
assert x['fixed_ports']==y['fixed_ports'] and x['positive_shift']==y['positive_shift']
assert len(x['gate_records'])==len(y['gate_records'])==60
mapping=list(range(1,27))+[None,27,None,28,29,None,30,None,31,32,None,33]
assert len(mapping)==38
text=(p/'Sign33Lift38.lean').read_text();part=text.split('def lift ',1)[1].split('theorem signed_values',1)[0]
m=re.search(r'!\[(.*?)\]',part,re.S);assert m
actual=[None if t.strip()=='0' else int(t.strip()[2:]) for t in m.group(1).split(',')]
assert actual==mapping
for i in range(1,15): assert mapping[i-1]==i
names=[]
for A,B in zip(x['gate_records'],y['gate_records']):
 assert all(A[k]==B[k] for k in ('kind','name','left','right','op'))
 if A['kind']!='materialized':continue
 names.append(A['name']); idx=lambda pos: mapping[pos-1]
 if 'sign_coordinate' not in B:
  assert idx(A['positive_coordinate'])==B['positive_coordinate'] and 'negative_coordinate' not in A
 else:
  s=B['sign']; v=B['sign_coordinate']
  assert (idx(A['positive_coordinate']),idx(A['negative_coordinate']))==((v,None) if s==1 else (None,v))
assert len(names)==19
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
print(json.dumps({'status':'PASS_EXTERNAL_MAPPING','source_sha256':h(p/'Sign33Lift38.lean'),'norm38_sha256':h(a),'sign33_sha256':h(b),'source_graph_sha256':x['source_graph_sha256'],'materialized_names':names,'full38_to_full33':mapping,'scope':'External syntax/coordinate comparison only; no Lean gate, norm, model, witness or source-equivalence proof.'},sort_keys=True,indent=2))
