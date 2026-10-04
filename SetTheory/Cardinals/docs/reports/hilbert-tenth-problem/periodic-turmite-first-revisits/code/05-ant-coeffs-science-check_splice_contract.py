#!/usr/bin/env python3
"""New read-only static contract check; never executes any old source/schedule."""
import json,pathlib,hashlib
ROOT=pathlib.Path(__file__).resolve().parent
EXPECTED_HASH={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}
prefix=json.loads((ROOT/'verification/full-prefix-receipt.json').read_text())
labels={f'tile:{j}' for j in range(576000)}|{f'first:{j}' for j in range(576000)}|{f'anchor:{j}' for j in range(584)}|set('Cu Cx Cbase C198 EndpointK EndpointD 0 1 2 3 4 6 8 9'.split())
assert len(labels)==prefix['coefficient_labels']==1152598
rows={}
for arity,name in [(2,'two'),(1,'one')]:
    old=json.loads((ROOT/f'data/main_receipts/{name}-input-receipt.json').read_text())
    assert old['source_sha256']==EXPECTED_HASH[arity]
    assert old['fixed_coefficient_port_count']==len(labels)
    cats=old['fixed_coefficient_categories']
    assert cats['tile_rows']==cats['first_column_rows']==576000 and cats['anchor_rows']==584
    assert set(cats['named'])==set('Cu Cx Cbase C198 EndpointK EndpointD'.split())
    assert old['ordinary_integer_literals']==[0,1,2,3,4,6,8,9]
    known=old['positive_witnesses'];raw=old['raw_positive_inputs']
    assert len(known)==len(set(known))==(465 if arity==2 else 467)
    assert not(set(known)&set(raw)) and all(not k.startswith('C:') for k in known+raw)
    assert raw==(['RawLeft','RawRight'] if arity==2 else ['RawInput'])
    if arity==1:assert known[:2]==['RawLeft','RawRight']
    main=old['single_polynomial'];N=prefix['source']['total']
    assert main['equations']==1 and main['exact_degree']==2304000
    rows[arity]={'M':prefix['source']['M']+main['M'],'A':prefix['source']['A']+main['A'],'total':N+main['total'],'positive_witnesses':len(known),'raw':raw,'old_stream_sha256':old['source_sha256'],'final_left_gate':N+old['sum_of_squares']['output'],'final_right_zero_gate':0,'coordinate_list_sha256':hashlib.sha256(json.dumps(known,separators=(',',':')).encode()).hexdigest()}
result={'status':'PASS_STATIC_FORMAL_SPLICE_CONTRACT','old_main_or_joined_stream_executed':False,'joined_stream_hash_claimed':False,'covered_coefficient_labels':len(labels),'arity_results':rows,'scope':'Exact formal binding/topology proof plus static authenticated-receipt inventory/count/domain check; not a joined-stream generation receipt.'}
print(json.dumps(result,indent=2))
