#!/usr/bin/env python3
"""Mutate each arithmetic gate once, independently of release check.py."""
import json
import audit_scalar as a
cases=[]
for f in sorted(a.ROOT.glob('*cofactor11_*.json')):
 p=json.loads(f.read_text());count=0
 for i,row in enumerate(p['nodes']):
  if row[0] not in ('add','sub','mul'):continue
  old=row[0];row[0]='sub' if old=='add' else 'add'
  try:a.local_audit(p)
  except (ValueError,KeyError):count+=1
  else:raise ValueError('accepted gate mutation '+str((f.name,i,old)))
  finally:row[0]=old
 cases.append({'name':p['name'],'every_arithmetic_gate_mutation_rejected':count})
result={'status':'PASS','cases':cases,'total_mutations':sum(x['every_arithmetic_gate_mutation_rejected'] for x in cases)}
(a.OUT/('ALL_GATE_MUTATIONS_OPTIMIZED.json' if not __debug__ else 'ALL_GATE_MUTATIONS.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
