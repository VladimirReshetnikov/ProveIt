#!/usr/bin/env python3
"""External candidate/source coordinate alignment; not a Lean model proof."""
import hashlib,json,re
from pathlib import Path
p=Path(__file__).resolve().parent;d=p.parents[1]
a=d/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
b=d/'research/nine-sharing-quartic65-sign33-candidate/seed.json'
x=json.loads(a.read_text());y=json.loads(b.read_text());assert x['source_graph_sha256']==y['source_graph_sha256']
A={r['name']:r for r in x['gate_records']}; B=[r for r in y['gate_records'] if r['kind']=='materialized'];assert len(B)==19
expected=[f'u {i}' for i in range(14)];signed={'gap':'gap','tau':'tau','cTminusR':'inner','V':'value','V2minusY2':'negative'}
for row in B:
 old=A[row['name']];assert old['kind']=='materialized';assert row['op']==old['op'] and row['left']==old['left'] and row['right']==old['right']
 pos=row.get('sign_coordinate',row.get('positive_coordinate'));assert pos==len(expected)+1
 if 'sign_coordinate' in row:
  assert row['name'] in signed and row['sign']==(-1 if row['name']=='V2minusY2' else 1)
  expected.append(signed[row['name']])
 else:
  assert 'negative_coordinate' not in old
  expected.append(f"w {old['positive_coordinate']-1}")
src=p/'src/DiophantineConsistency/SharingForward33.lean';part=src.read_text().split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0];m=re.search(r'!\[(.*?)\]',part,re.S);assert m
actual=[x.strip() for x in m.group(1).split(',')];assert actual==expected and len(actual)==33
H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
print(json.dumps({'status':'PASS_EXTERNAL_CONSTRUCTOR_MAPPING','source_sha256':H(src),'sign33_json_sha256':H(b),'norm38_json_sha256':H(a),'witness_coordinates':actual,'scope':'Source-level vector and external candidate materialized-coordinate/sign correspondence only; no Lean elaboration, gate equations, five norms, source-zero implication or iPRA.'},sort_keys=True,indent=2))
