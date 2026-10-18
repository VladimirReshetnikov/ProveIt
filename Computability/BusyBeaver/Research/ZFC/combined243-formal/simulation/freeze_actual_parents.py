#!/usr/bin/env python3
"""Own inert metadata writer: builds a guard only from actual PASS parent pins."""
from pathlib import Path
import argparse,hashlib,json,re,ast,difflib
B=Path('/tmp/zfc243-combined-lean');P=B/'simulation'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--invariant-record',type=Path,required=True);p.add_argument('--invariant-sha',required=True)
p.add_argument('--blocks-record',type=Path,required=True);p.add_argument('--blocks-sha',required=True)
a=p.parse_args()
selected={'positive':(Path('/tmp/zfc244-positive-blocks/run2/verification.json'),'39d7b8257fc41468782322c1131e81c8ffdef34edccd61ec539419a205bdd420',4,4),'invariant':(a.invariant_record,a.invariant_sha,5,8),'blocks':(a.blocks_record,a.blocks_sha,14,14)}
parents={};pool={};tools={};compiler=None
for key,(path,h,np,nc) in selected.items():
 assert sha(path)==h;e=json.loads(path.read_text());assert e['status']=='PASS' and (e['named_axiom_probes'],e['callers'],e['warnings'])==(np,nc,0)
 assert e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms']
 for q,v in e['before'].items():assert sha(q)==v
 if compiler is None:compiler=e['compiler']
 assert all(compiler[k]==e['compiler'][k] for k in ['path','sha256','version'])
 f=e['fresh_modules'][0];assert len(e['fresh_modules'])==1 and sha(f['path'])==f['sha256']
 assert e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0)
 assert e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']}
 for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
  q={k:q[k] for k in ['module','source','source_sha256','object','object_sha256']}
  for k in ['source','object']:assert sha(q[k])==q[k+'_sha256']
  assert q['module'] not in pool or pool[q['module']]==q;pool[q['module']]=q
 for q in e['toolchain_providers']:
  q={k:q[k] for k in ['module','object','object_sha256']};assert sha(q['object'])==q['object_sha256']
  assert q['module'] not in tools or tools[q['module']]==q;tools[q['module']]=q
 names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
 assert names==[q['name'] for q in e['axiom_reports']] and len(names)==np
 parents[key]=dict(**d(path),probes=np,callers=nc,audit_names=names,report_names=names,tools=sorted(q['module'] for q in e['toolchain_providers']))
assert set(pool)=={'BusyBeaver.Core','BusyBeaver.ZFC.RuntimePerm252','BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.TableRotation244','BusyBeaver.ZFC.TableCombined243','BusyBeaver.ZFC.Rotation244Invariant','BusyBeaver.ZFC.Combined243Blocks'}
assert set(tools)=={'Init','Lean.Elab.Tactic.Omega'}
static=[d(B/'prepare_ports.py'),d(B/'source-inventory.json'),d(P/'check-template.py'),d(P/'guard-proposal.json'),d(Path(__file__)),d(B/'independent-port-source-review.json')]
boundary=dict(parents=parents,compiler=compiler,reused_modules=list(pool.values()),toolchain_providers=list(tools.values()),scope='Exact three actual fresh prerequisite records and their seven-project union; small parent snapshots rehashed. No broad calibration or PA endpoint claim.',static_inputs=static)
assert not (P/'check.py').exists() and not (P/'boundary.json').exists()
(P/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
s=(P/'check-template.py').read_text()
for key,value in [('BOUNDARY_SHA',sha(P/'boundary.json')),('PARENT_SHAS',{k:v['sha256'] for k,v in parents.items()})]:
 s,n=re.subn(r'^'+key+r'=.*$',lambda m:key+'='+repr(value),s,count=1,flags=re.M);assert n==1
line="    require(BOUNDARY_SHA is not None, 'Pending actual predecessor proof: this template is not executable.')\n"
assert s.count(line)==1;s=s.replace(line,'')
s=s.replace('Concrete compensated244 whole-run simulation; exact three parents/seven projects.','Concrete Combined243 versus Rotation244 whole-run simulation; exact three parents/seven projects.')
s=s.replace('Concrete244 versus checked245 positive-block simulation, arbitrary finite-support start tapes and exact blank halting/nonhalting iff. No PA internalization or infinite-support tape claim.','Combined243 versus Rotation244 positive-block simulation, arbitrary finite-support start tapes and exact blank halting/nonhalting iff. No consistency calibration, PA internalization or infinite-support tape claim.')
ast.parse(s);(P/'check.py').write_text(s)
(P/'guard-actual-freeze.diff').write_text(''.join(difflib.unified_diff((P/'check-template.py').read_text().splitlines(True),s.splitlines(True),fromfile='check-template.py',tofile='check.py')))
(P/'guard-freeze.json').write_text(json.dumps(dict(status='ACTUAL_PARENT_GUARD_SOURCE_ONLY_NOT_EXECUTED',guard=d(P/'check.py'),boundary=d(P/'boundary.json'),parents=parents,source=d(P/'Combined243Simulation.lean'),audit=d(P/'Audit.lean'),projects=7,tools=sorted(tools),probes=4,callers=4,writer=d(__file__),prepare_command=['python3','-B',str(P/'check.py'),'--output',str(P/'prepared1'),'--prepare-only'],actual_command=['python3','-B',str(P/'check.py'),'--output',str(P/'run1')]),indent=2)+'\n')
print(json.dumps({'guard':d(P/'check.py'),'boundary':d(P/'boundary.json'),'freeze':d(P/'guard-freeze.json')},indent=2))
