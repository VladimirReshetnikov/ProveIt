#!/usr/bin/env python3
"""Own source/metadata writer. Emits guards; never invokes a guard or compiler."""
from pathlib import Path
import hashlib,json,re,difflib,ast
B=Path('/tmp/zfc243-combined-lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
def replace(t,a,b,n=1):
 assert t.count(a)==n,(a,t.count(a),n)
 return t.replace(a,b)
def assignment(t,key,value):
 t,n=re.subn(r'^'+key+r'=.*$',lambda m:key+'='+repr(value),t,count=1,flags=re.M)
 assert n==1;return t
base=Path('/tmp/zfc244-compensated-lean/blocks/check.py');raw=base.read_text()
inventory=json.loads((B/'source-inventory.json').read_text())
unit={u['name']:u for u in inventory['units']}
parent=B/'table-rotation/run2/verification.json';e=json.loads(parent.read_text())
assert sha(parent)=='339ac1eb684bf2b0e2dca81f6a5d693abf2f3fe7079d0c924e5cf2ab870f3466'
assert e['status']=='PASS' and (e['named_axiom_probes'],e['callers'])==(7,7)
for p,h in e['before'].items():assert sha(p)==h
f=e['fresh_modules'][0]
for p,h in [(f['path'],f['sha256']),(e['source']['path'],e['source']['sha256'])]:assert sha(p)==h
reused=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
assert {x['module'] for x in reused}=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}
static=[d(B/'source-inventory.json'),d(B/'prepare_ports.py'),d(Path(__file__)),d(B/'independent-port-source-review.json'),d(B/'independent-table-source-review.json')]
boundary={'parent':d(parent),'compiler':e['compiler'],'reused_modules':reused,'toolchain_providers':e['toolchain_providers'],
 'scope':'Exact passed Rotation244 fresh object with pre-audit capture, plus its checked Core and Init providers. No broad endpoint revalidation.',
 'static_inputs':static}
p=B/'invariant';(p/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
t=raw.replace('/tmp/zfc244-compensated-lean/blocks',str(p)).replace('Compensated244Blocks','Rotation244Invariant').replace('TableCompensated244','TableRotation244')
t=replace(t,'Seven exact compensated244 blocks and their endpoints; three project providers.','Rotation244 local tape invariant; exact Core+Rotation244 and Init providers.')
u=unit['Rotation244Invariant']
for k,v in [('SOURCE_SHA',u['source']['sha256']),('AUDIT_SHA',u['audit']['sha256']),('BOUNDARY_SHA',sha(p/'boundary.json')),('PARENT_SHA',sha(parent)),('PROBES',[x.rsplit('.',1)[1] for x in u['qualified_probes']])]:t=assignment(t,k,v)
t=replace(t,"(e['named_axiom_probes'],e['callers'])==(53,6)","(e['named_axiom_probes'],e['callers'])==(7,7)")
t=replace(t,'len(ns)==53','len(ns)==7')
t=replace(t,"==14,'Typed callers changed.'","==8,'Typed callers changed.'")
t=replace(t,"len(reused)==3 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.TableRotation244'}","len(reused)==2 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}")
t=replace(t,"{q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'}","{q['module']for q in tools}=={'Init'}")
t=replace(t,"scope='Seven paired positive blocks and seven new endpoint identities on arbitrary Core finite-support tapes; explicit finite read premises; no whole-run theorem.'","scope='Local invariant at old68/81/167 on arbitrary Core finite-support tapes, preserved for every natural run duration. No calibration or machine comparison.'")
t=replace(t,'exact_project_prerequisite_count=3','exact_project_prerequisite_count=2')
t=replace(t,'named_axiom_probes=14,callers=14','named_axiom_probes=5,callers=8')
t=replace(t,"require(not obj.exists(),'Target already exists.');run('source',ss,obj)","require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)")
ast.parse(t);(p/'check.py').write_text(t)
(p/'guard-from-checked-blocks.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(True),t.splitlines(True),fromfile=str(base),tofile=str(p/'check.py'))))
(p/'guard-freeze.json').write_text(json.dumps({'status':'SOURCE_ONLY_GUARD_FROZEN_NOT_EXECUTED','guard':d(p/'check.py'),'boundary':d(p/'boundary.json'),'source':u['source'],'audit':u['audit'],'parent':d(parent),'projects':2,'tools':['Init'],'probes':5,'callers':8,'prepare_command':['python3','-B',str(p/'check.py'),'--output',str(p/'prepared1'),'--prepare-only'],'actual_command':['python3','-B',str(p/'check.py'),'--output',str(p/'run1')],'writer':d(__file__),'template':d(base),'scope':'Strict exact current parent and fresh-first checks; shared120 seconds, -j1, -M4096, default proof limits. No guard/compiler/version invocation by author.'},indent=2)+'\n')

# Pending proposals refuse execution until exact new parent and boundary pins exist.
for folder,name in [('blocks','Combined243Blocks'),('simulation','Combined243Simulation')]:
 p=B/folder;u=unit[name]
 bp=base if folder=='blocks' else Path('/tmp/zfc244-compensated-lean/simulation/check.py')
 before=bp.read_text();t=before.replace('/tmp/zfc244-compensated-lean/'+folder,str(p)).replace('Routing245','Rotation244').replace('Compensated244','Combined243')
 for k,v in [('SOURCE_SHA',u['source']['sha256']),('AUDIT_SHA',u['audit']['sha256']),('BOUNDARY_SHA',None)]:t=assignment(t,k,v)
 if folder=='blocks':t=assignment(t,'PARENT_SHA',None)
 else:
  t=assignment(t,'PARENT_SHAS',{'positive':'39d7b8257fc41468782322c1131e81c8ffdef34edccd61ec539419a205bdd420','invariant':None,'blocks':None})
  special="        if key=='invariant':\n            require(desc['report_names']==['SetTheory.BusyBeaver.ZFC.Rotation244Invariant.'+n for n in ns]and 'open SetTheory.BusyBeaver.ZFC.Rotation244Invariant' in Path(e['audit']['snapshot']).read_text(),'Unexpected invariant namespace.')\n        else:require(desc['report_names']==ns,'Unexpected parent namespace.')"
  t=replace(t,special,"        require(desc['report_names']==ns,'Unexpected parent namespace.')")
 t=replace(t,"a=p.parse_args();require(__debug__,'No optimized Python.')","a=p.parse_args();require(__debug__,'No optimized Python.')\n    require(BOUNDARY_SHA is not None, 'Pending actual predecessor proof: this template is not executable.')")
 t=replace(t,"require(not obj.exists(),'Target already exists.');run('source',ss,obj)","require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)")
 ast.parse(t);(p/'check-template.py').write_text(t)
 (p/'guard-template.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),t.splitlines(True),fromfile=str(bp),tofile=str(p/'check-template.py'))))
 (p/'guard-proposal.json').write_text(json.dumps({'status':'PENDING_ACTUAL_PARENTS_SOURCE_ONLY','guard_template':d(p/'check-template.py'),'source':u['source'],'audit':u['audit'],'probes':u['probes'],'callers':u['callers'],'projects':3 if folder=='blocks' else7,'new_parent_hashes':None,'new_parent_objects':None,'tools':['Init','Lean.Elab.Tactic.Omega'],'existing_positive_parent':'39d7b8257fc41468782322c1131e81c8ffdef34edccd61ec539419a205bdd420' if folder=='simulation' else None,'freeze_policy':'After actual predecessors PASS, derive exact provider union/DFS and current hashes from those records; preserve this template and emit separate check.py plus boundary. No future object or verification hash is guessed.','template':d(bp),'writer':d(__file__)},indent=2)+'\n')
print(json.dumps({'invariant_guard':d(B/'invariant/check.py'),'invariant_boundary':d(B/'invariant/boundary.json'),'pending_blocks':d(B/'blocks/check-template.py'),'pending_simulation':d(B/'simulation/check-template.py')},indent=2))
