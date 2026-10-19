"""Re-derive instruction rules under the checked source zero/nonzero invariant.
Any free rows are research leads only; full adapted machine proofs remain necessary.
"""
from pathlib import Path
import json,inspect,hashlib,time,sys
import symbolic_runtime as s
ROOT=Path(__file__).resolve().parents[1]
table=s.r.table(ROOT/'baseline/rotation240/zfc_rotation240_old.tm')
sites=json.loads((ROOT/'baseline/rotation240/sites_logical.json').read_text())
s.validate_inputs(table,sites)
abstract_path=ROOT/'semantic/abstract_zeros.json'
facts=json.loads(abstract_path.read_text())['states']
assert len(facts)==len(sites)
# This adapter retains the baseline positive-CD parametrization v+1.
# A separately known-positive tested register would otherwise be shifted twice.
# The supplied fixed point has no such cases; reject other fact sets explicitly.
assert all(f is None or op != 'CD' or f[arg] != 2
           for (_, op, arg), f in zip(sites, facts))
source=inspect.getsource(s.case)
source=source.replace('def case(table,lemmas,site,positive,append=1,keep_trace=False):','def restricted_case(table,lemmas,site,positive,facts,append=1,keep_trace=False):')
needle='    values=[var(2+i) for i in range(9)]\n'
assert source.count(needle)==1
source=source.replace(needle,needle+'    values=[ZERO if f==1 else add(num(1),v) if f==2 else v for f,v in zip(facts,values)]\n')
context=dict(vars(s));exec(compile(source,'<restricted-case-adapter>','exec'),context)
case=context['restricted_case'];lemmas,blocks=s.prove_blocks(table)
rows=set();cases=0;skipped=0;started=time.monotonic();rules=0
for i,site in enumerate(sites):
 for positive in ((False,True) if site[1]=='CD' else (False,)):
  if facts[i] is None or (site[1]=='CD' and not (facts[i][site[2]] & (2 if positive else 1))):
   skipped+=1;continue
  a=case(table,lemmas,site,positive,facts[i]);rows.update(a['rows']);cases+=1;rules+=a['symbolic_steps']
 if i%1000==0:print('checked',cases,'cases',round(time.monotonic()-started,2),'seconds',flush=True)
for block in blocks:
 for event in block['trace']:
  if event[0]!='list':rows.add(tuple(event[1][:2]))
out={'status':'RESTRICTED_UNBOUNDED_RUNTIME_PASS','cases':cases,'skipped_guards':skipped,'symbolic_rules':rules,
 'unqueried_rows':sorted(set(table)-rows),'queried_rows':len(rows),'seconds':time.monotonic()-started,
 'source_sha256':hashlib.sha256((ROOT/'baseline/rotation240/sites_logical.json').read_bytes()).hexdigest(),
 'abstract_record_sha256':hashlib.sha256(abstract_path.read_bytes()).hexdigest(),
 'scope':'Unbounded literal-table symbolic rules under the supplied source abstract invariant; a free row would require proof that its change is absent from startup and preserves the macro contract.'}
(ROOT/'validation/restricted_runtime.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
