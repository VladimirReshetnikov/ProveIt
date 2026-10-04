#!/usr/bin/env python3
"""Independent complete ledger from previously checked finite data/receipts."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
o=json.loads((HERE/'receipt.json').read_text())['occurrences']
p=json.loads((HERE/'profiles-receipt.json').read_text())['cache']
f=json.loads(Path('/workspace/shared/ant-coefficient-compression/full-prefix-receipt.json').read_text())
def cost(n):return n.bit_length()+n.bit_count()-2 if n>1 else 0
R=601547591;V=240619037200;U=2*V;S=576000
bits=R.bit_length()-1;ones=R.bit_count()-1
stages={
    'occurrences':o['source'],
    'small_profiles_and_basic_literals':{'M':p['Horner_M'],'A':p['Horner_A']+2},
    'geometric_sum_and_fixed_shifts':{'M':2*bits+ones+sum(map(cost,[375,V-425,V-400,V-25,U-25])),'A':bits+ones},
    'operation_corrections':{'M':957*sum(p['correction_columns'].values()),'A':957*sum(p['correction_columns'].values())},
    'bulk_boundary_and_period_join':{'M':7*S,'A':7*S},
    'anchor_rows':{'M':584*220,'A':584*220},
    'remaining_named_constants':{'M':sum(map(cost,[U,U-219,198,481225262775]))+1,'A':5}}
for name,counts in stages.items():
    counts['total']=counts['M']+counts['A']
    if counts!=f['stages'][name]:raise ValueError((name,counts,f['stages'][name]))
counts={'M':sum(v['M'] for v in stages.values()),'A':sum(v['A'] for v in stages.values())}
counts['total']=counts['M']+counts['A']
if counts!={'M':13182377,'A':15898997,'total':29081374}:raise ValueError(counts)
result={'status':'PASS_INDEPENDENT_CLOSED_COUNTS','stages':stages,'total':counts}
(HERE/'closed-count-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
