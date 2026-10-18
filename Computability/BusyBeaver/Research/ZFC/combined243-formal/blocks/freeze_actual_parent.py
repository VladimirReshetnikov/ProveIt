#!/usr/bin/env python3
"""Own source/metadata writer only; never invokes a guard or compiler."""
from pathlib import Path
import hashlib,json,re,ast,difflib
B=Path('/tmp/zfc243-combined-lean');P=B/'blocks'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
E=B/'table-combined/run1/verification.json';H='3aa2fbcd854242ec36086af6cce69ad8b0e00c949f8c2d67a5c28dd025cb175d'
assert sha(E)==H;e=json.loads(E.read_text());assert e['status']=='PASS'
assert (e['named_axiom_probes'],e['callers'],e['warnings'])==(53,6,0)
assert e['before']==e['after'] and e['all_input_provider_postchecks']
for p,h in e['before'].items():assert sha(p)==h
f=e['fresh_modules'][0];assert sha(f['path'])==f['sha256']
reused=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
assert {q['module'] for q in reused}=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244','BusyBeaver.ZFC.TableCombined243'}
static=[d(B/'source-inventory.json'),d(B/'prepare_ports.py'),d(P/'check-template.py'),d(P/'guard-proposal.json'),d(Path(__file__)),d(B/'independent-port-source-review.json'),d(B/'independent-table-source-review.json')]
boundary=dict(parent=d(E),compiler=e['compiler'],reused_modules=reused,toolchain_providers=e['toolchain_providers'],static_inputs=static,scope='Exact passed Combined243 table fresh object with pre-audit capture and its Core/Rotation244/Init/Omega providers. No broad ancestor revalidation.')
assert not (P/'check.py').exists() and not (P/'boundary.json').exists()
(P/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
s=(P/'check-template.py').read_text()
for key,value in [('PARENT_SHA',H),('BOUNDARY_SHA',sha(P/'boundary.json'))]:
 s,n=re.subn(r'^'+key+r'=None$',key+'='+repr(value),s,flags=re.M);assert n==1
line="    require(BOUNDARY_SHA is not None, 'Pending actual predecessor proof: this template is not executable.')\n"
assert s.count(line)==1;s=s.replace(line,'')
ast.parse(s);(P/'check.py').write_text(s)
(P/'guard-actual-freeze.diff').write_text(''.join(difflib.unified_diff((P/'check-template.py').read_text().splitlines(True),s.splitlines(True),fromfile='check-template.py',tofile='check.py')))
(P/'guard-freeze.json').write_text(json.dumps(dict(status='ACTUAL_PARENT_GUARD_SOURCE_ONLY_NOT_EXECUTED',guard=d(P/'check.py'),boundary=d(P/'boundary.json'),parent=d(E),source=d(P/'Combined243Blocks.lean'),audit=d(P/'Audit.lean'),projects=3,tools=['Init','Lean.Elab.Tactic.Omega'],probes=14,callers=14,writer=d(__file__),prepare_command=['python3','-B',str(P/'check.py'),'--output',str(P/'prepared1'),'--prepare-only'],actual_command=['python3','-B',str(P/'check.py'),'--output',str(P/'run1')],scope='Shared 120s source+audit; -j1 -M4096; default proof limits; exact fresh-before-audit and provider bindings; no supplied execution by author.'),indent=2)+'\n')
print(json.dumps({'guard':d(P/'check.py'),'boundary':d(P/'boundary.json'),'freeze':d(P/'guard-freeze.json')},indent=2))
