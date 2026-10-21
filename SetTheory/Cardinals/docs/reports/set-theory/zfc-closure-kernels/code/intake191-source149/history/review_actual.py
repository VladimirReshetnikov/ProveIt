"""Own bounded terminal-record audit, not a repeated supplied checker run."""
from pathlib import Path
import json,hashlib
O=Path('/tmp/zfc-intake191-independent-review');P=Path('/tmp/zfc-intake191-source149-run1');C=P/'copy'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
actual=read(P/'actual.json')
assert actual['status']=='SELECTED_LEAVES_EXITED_ZERO'and actual['inputs_unchanged']and len(actual['jobs'])==8
assert all(j['returncode']==0 and not j['timed_out']for j in actual['jobs'])
for j in actual['jobs']:
 assert sha(Path(j['stdout']))==j['stdout_sha256']and sha(Path(j['stderr']))==j['stderr_sha256']
 assert Path(j['stderr']).read_bytes()==b''
logic=[read(P/'logs'/f'{name}.stdout')for name in ('logic-shared','logic-independent')]
for x in logic:
 assert x['verified']is True and x['proof_nodes']==3728 and x['shared_terms']==5160 and x['roots']['rho8']==3727
 assert x['rules']==dict(dominated_rho8=1260,truth=1,mp_substitution=55,substitution=410,mp=2002)
assert logic[0]['maximum_subterm_depth']==4 and logic[0]['roots']==logic[1]['roots']
source=read(P/'results/source/source_receipt.json');ind_source=read(P/'logs/source-independent.stdout')
assert source['outside_ax_preservation']['primitive_leaves']==186 and source['equivalent_source']['guarded_cases']==6176 and ind_source['verified']is True
assert source['equivalent_source']['metrics']==dict(dag_nodes=203,leaf_occurrences=4751,maximum_depth=45,maximum_zero_run=6)
assert (P/'results/source/dominated_zyx206.json').read_bytes()==(C/'source/dominated_zyx206.json').read_bytes()
assert (P/'results/rebuilt.native.tm').read_bytes()==(C/'binary/machine/k218.native.tm').read_bytes()
compact=read(P/'logs/compact-bijection.stdout');assert compact['verified']is True and compact['working_states']==218 and compact['transition_rows']==436
runtime=read(P/'results/runtime/runtime.json');cases=read(P/'results/runtime/runtime_cases.json');startup=read(P/'results/runtime/startup.json');blank=read(P/'logs/blank-independent.stdout')
sites=read(C/'binary/machine/sites218.json')
assert runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS'and runtime['failures']==[]and runtime['expected_cases']==runtime['proved_cases']==len(cases)==6176
assert runtime['table_sha256']==sha(C/'binary/machine/k218.native.tm')and runtime['sites_sha256']==sha(C/'source/sites218.json')
assert [(c['site_index'],c['positive'])for c in cases]==[(i,pos)for i,s in enumerate(sites)for pos in ((False,True)if s[1]=='CD'else(False,))]
assert all(c['duration'][0]>0 and all(v>=0 for v in c['duration'])for c in cases)
assert len(runtime['blocks'])==4 and all(x['arbitrary_contexts']is True for x in runtime['blocks'])
table={}
for line in (C/'binary/machine/k218.native.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();table[int(q),int(b)]=(int(w),d,int(z))
mapping={int(k):v for k,v in read(C/'binary/code/inputs/legacy_mapping.json').items()}
for q in {q for q,b in table}|{254}:mapping.setdefault(q,q+1000)
inverse={v:k for k,v in mapping.items()}
used={tuple(r)for c in cases for r in c['rows']}
for block in runtime['blocks']:
 for event in block['trace']:
  if event[0]in ('literal','unary'):used.add(tuple(event[1][:2]))
native_used={(inverse[q],b)for q,b in used}
assert native_used==set(table)
assert startup['status']=='CALIBRATED_DIRTY_ROOT_SEED'and startup['steps']==312605 and startup['state']==84 and startup['head']==-5 and startup['gap']==80
assert startup['registers']==[3,0,0,0,3,0,0,0,0]and startup['spares']==[1]*130 and len(startup['one_cells'])==277
assert blank['verified']is True and blank['steps']==startup['steps']and blank['head']==startup['head']and blank['additional_gap']==startup['gap']
assert blank['complete_one_cells']==startup['one_cells']and blank['logical_registers']==startup['registers']and blank['spare_values']==startup['spares']
assert (P/'results/runtime/runtime_cases.json').read_bytes()==(C/'binary/validation/runtime_cases.json').read_bytes()
assert (P/'results/runtime/startup.json').read_bytes()==(C/'binary/validation/startup.json').read_bytes()
proof_steps=sum(c['symbolic_steps']for c in cases)
assert proof_steps==1616989 and min(c['duration'][0]for c in cases)==13
report=dict(status='FRESH_SELECTED_SOURCE149_CHECKS_PASS',findings=[],reviewer_role='Independent manuscript/source reviewer; ran only the eight explicitly authorized submitted leaves on a disposable copy, then own bounded actual-record audit. Not original proof/candidate author.',actual=dict(path=str(P/'actual.json'),sha256=sha(P/'actual.json')),reviewer_source=dict(path=str(Path(__file__)),sha256=sha(Path(__file__))),selected_jobs=8,code_and_data_inputs_unchanged=True,all_processes_exit_zero=True,all_stderr_empty=True,logic=dict(proof_nodes=3728,shared_terms=5160,root=3727,two_forward_checkers=True),source=dict(DAG=203,leaves=4751,depth=45,zero_run=6,unchanged_outside_AX_paths=186),runtime=dict(guarded_cases=6176,symbolic_steps=proof_steps,minimum_duration_constant=13,maximum_symbolic_steps=max(c['symbolic_steps']for c in cases),all_native_rows=len(native_used),seconds=runtime['seconds'],four_exact_table_list_schemas=True),startup=dict(steps=312605,state=84,head=-5,gap=80,registers=startup['registers'],spares=130,ones=277,complete_tape_agrees_between_drivers=True),delivered_case_and_trace_bytes_reproduced=True,scope='Ordinary mathematical/executable symbolic evidence. No new Lean/Rocq/internal PA endpoint, unconditional nonhalting, minimality or <=217 result; inherited numerical-calculus/ZFC calibration remains an explicit dependency.')
(O/'actual-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
