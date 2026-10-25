#!/usr/bin/env python3
"""Deliberately alter every arithmetic gate; independent verifier must reject."""
import copy,json
from pathlib import Path
import check
ROOT=Path(__file__).resolve().parent
results=[]
for path in sorted(ROOT.glob('integer11_degree*_ops*.json')):
 p=json.loads(path.read_text());checked=0
 for i,row in enumerate(p['nodes']):
  if row[0] not in ('add','sub','mul'):continue
  for replacement in ('add','sub','mul'):
   if replacement==row[0]:continue
   damaged=copy.deepcopy(p);damaged['nodes'][i][0]=replacement
   try:check.local_checks(damaged)
   except (ValueError,KeyError,IndexError):checked+=1
   else:raise ValueError('unrejected arithmetic mutation '+path.name+' node '+str(i)+' '+replacement)
 results.append({'name':p['name'],'arithmetic_gates':p['operations'],'all_alternative_operation_mutations_rejected':checked})
out={'status':'PASS','assertions_enabled':__debug__,'equations':results}
(ROOT/('MUTATIONS.json' if __debug__ else 'MUTATIONS_OPTIMIZED.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
