#!/usr/bin/env python3
"""Read-only independent gate/liveness audit of strongest pinned comparators."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
files=[
'38-batching11/eleven/generated/absorbed_index_eleven_translated_product.json',
'38-batching11/eleven/generated/absorbed_index_eleven_translated_shifted_system.json',
'38-batching11/eleven/generated/absorbed_index_eleven_product.json',
'38-batching11/eleven/generated/absorbed_index_eleven_shifted_system.json',
'44-b4-sparse/positive/full_product.json',
'44-b4-sparse/positive/full_shifted_system.json',
'44-b4-sparse/positive/short_product.json',
'44-b4-sparse/positive/short_shifted_system.json']
rows=[]
for name in files:
    raw=(HERE/'sources'/name).read_bytes(); d=json.loads(raw)
    seen=set(d['witnesses']+d['fixed_numerals'])
    for out,op,a,b in d['source']:
        if out in seen or op not in '+-*': raise ValueError('DAG syntax')
        if any(isinstance(t,str) and t not in seen for t in (a,b)): raise ValueError('DAG reference')
        seen.add(out)
    live={d['output']} if 'output'in d else {t for pair in d['comparisons'] for t in pair if isinstance(t,str)}
    for out,op,a,b in reversed(d['source']):
        if out in live:live.update(t for t in (a,b) if isinstance(t,str))
    if any(row[0] not in live for row in d['source']):raise ValueError('dead gate')
    if any(v not in live for v in d['witnesses']+d['fixed_numerals']):raise ValueError('dead supplied input')
    if len(d['source'])!=d['ledger']['operations']:raise ValueError('count mismatch')
    rows.append({'file':name,'sha256':sha256(raw).hexdigest(),'domain':d['domain'],'witness_count':len(d['witnesses']),'equations':1 if 'output'in d else len(d['comparisons']),'live_operations':len(d['source']),'operator_counts':dict(Counter(row[1] for row in d['source'])),'degree_claim':d.get('residual_exact_degrees',d.get('exact_degree')),'degree_status':'Pinned ordinary proof inspected; not re-derived by this finite gate audit'})
result={'status':'PASS','scope':'Literal DAG operation count, domain/witness lists and complete liveness; no upstream program run','variants':rows}
(HERE/'VARIANT_LEDGER_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
