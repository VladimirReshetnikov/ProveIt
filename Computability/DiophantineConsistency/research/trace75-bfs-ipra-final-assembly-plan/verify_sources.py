#!/usr/bin/env python3
"""Read-only source and dependency-order check; never invokes Lean."""
from hashlib import sha256
from pathlib import Path
import json,re,sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
D=H.parents[1]
PLAN=H/'plan.json'
def need(b,m):
    if not b: raise RuntimeError(m)
def digest(p): return sha256(p.read_bytes()).hexdigest()
need(digest(PLAN)=='04559737ca02dc639ea0ac3a24bfd72997a9bae1f38c6d42b4da944b6a751dd6','plan drift')
plan=json.loads(PLAN.read_text())
need(plan['status']=='HELD_AWAITING_FORWARD_RESULT_AND_OUTER_EXIT','plan status')
need(plan['parent_result_sha256']=='TO_BE_PINNED_AFTER_TERMINAL_AND_AUDIT','parent result unexpectedly pinned')
need(plan['parent_outer_sha256']=='TO_BE_PINNED_AFTER_TERMINAL_AND_AUDIT','parent outer unexpectedly pinned')
canonical=D/plan['canonical_syntax_source']
need(digest(canonical)==plan['canonical_syntax_sha256'],'canonical syntax source drift')
names=[row['module'] for row in plan['stages']]
need(len(names)==5 and len(set(names))==5,'stage names')
records=[]
for index,row in enumerate(plan['stages']):
    source=D/row['source']; data=source.read_bytes()
    need(sha256(data).hexdigest()==row['sha256'],'source drift '+row['module'])
    imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',data.decode(),re.M)
    need(imports==row['imports'],'source imports drift '+row['module'])
    need(all(dep not in names[index:] for dep in imports),'dependency is not earlier '+row['module'])
    records.append({'module':row['module'],'sha256':row['sha256'],'imports':imports})
need((D/plan['stages'][0]['source']).read_bytes()==canonical.read_bytes()+
    b'\n#print axioms DiophantineConsistency.TenPositiveTrace75.evalRing_expression\n',
    'syntax instrumentation differs from canonical source')
print(json.dumps({'status':'PASS','scope':'source bytes and declared order only; no Lean or parent audit',
                  'plan_sha256':digest(PLAN),'stages':records},sort_keys=True))
