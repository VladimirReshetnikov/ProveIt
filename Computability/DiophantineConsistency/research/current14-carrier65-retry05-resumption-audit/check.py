#!/usr/bin/env python3
"""Read-only snapshot check of retry05 and historical endpoint; no Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]; ROOT=D.parents[1]
P=D/'research/current14-coherent-extension-refactor-retry05-runner'
A=P/'attempt01'; LIVE=Path('/tmp/current14-coherent490-refactor-retry05-20261110')
H=D/'research/current14-quoted-translated-endpoint-check/attempt01'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def pinned(path,digest):
 assert sha(path)==digest,str(path)
 return path.read_text()
runner=pinned(P/'run.py','f025f9fdf7ec59762faab7d135bed4bff50fe841f08397c0d126f83236d3e84e')
plan=json.loads(pinned(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c'))
state=json.loads(pinned(A/'state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82'))
outer=json.loads(pinned(A/'outer-result.json','11e4abc49bceea5a05faaab13d56a1dacdebe4ec5c4b32742633288b657df4a7'))
audit=json.loads(pinned(D/'reviews/current14-coherent-extension-refactor-retry05-failure-independent/result.json','f1ba44ecb50cb5f4d1f59ea3b2aef4a215d4f0d83fc7d1d12482adb5b4e24068'))
history=json.loads(pinned(D/'reviews/current14-quoted-translated-endpoint-terminal-independent/result.json','0c7e369ef1210e398d857dac5851836f93c9819db69874a4fba2ccd6efe5d957'))
qouter=json.loads((H/'outer-result.json').read_text()); qstate=json.loads(pinned(H/'state.json','65b86435269571d8b9e1439e45dd56cd8605939823d9e7e25ead6c8c8a90815b'))
assert qouter['outer_exit_code']==0 and qouter['outer_session']==48120 and qouter['state_sha256']=='65b86435269571d8b9e1439e45dd56cd8605939823d9e7e25ead6c8c8a90815b'
assert qstate['status']=='PASS' and history['status']=='PASS_TERMINAL_AUDIT' and history['outer_session']==48120
assert state['status']==outer['status']=='FAILED' and state['failure']==outer['failure']=="Refusal('disk_floor')"
assert outer['outer_exit_code']==1 and audit['status']=='PASS_INDEPENDENT_STOP_AUDIT'
assert sha(LIVE/'state.json')==sha(A/'state.json') and len(state['base_links'])==1000
entries=plan['entries'];rows=state['rows'];assert len(entries)==529 and len(rows)==240
assert len(outer['captured_logs'])==478
for i,(entry,row) in enumerate(zip(entries[:239],rows[:239])):
 assert entry['module']==row['module'] and entry['source_sha256']==row['source_sha256']
 obj=LIVE/'lib'/(row['module'].replace('.','/')+'.olean')
 assert obj.is_file() and sha(obj)==row['object_sha256']
 for kind in ('deps','compile'):
  child=row[kind];name=Path(child['log']).name
  assert child['exit']==0 and child['stop_reason'] is None and not child['monitor_errors'] and not child['observed_descendant_pids']
  assert sha(A/'logs'/name)==child['log_sha256']==outer['captured_logs'][name]
last=rows[-1];n='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert entries[239]['module']==last['module']==n and all(k not in last for k in ('deps','compile','object_sha256'))
assert not (LIVE/'lib'/(n.replace('.','/')+'.olean')).exists() and not list((LIVE/'logs').glob('239-*'))
assert audit['successful_stages']==239 and audit['next_stage']==n and not audit['next_child_started']
assert 'if require_fresh:need(not os.path.lexists(OUT)' in runner
assert "state=create_owned_state(OUT)" in runner and 'for index,e in enumerate(entries):' in runner
assert 'DISK_FLOOR=5_100_000_000' in runner and "need(len(completed)==530" in runner
client=pinned(P/'Current14CoherentAudit.lean','b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e')
for name in ('quoted_translated_endpoint','positive_zero_iff_zfc_refutation','ObjectCurrentEquation2011.eval_expression'):
 assert '#print axioms' in client and name in client
endpoint=pinned(D/'research/current14-quoted-translated-endpoint-draft/Current14QuotedTranslatedEndpoint.lean','90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965')
assert 'standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ' in endpoint
positions={e['module']:i+1 for i,e in enumerate(entries)}
assert positions['DiophantineConsistency.Current14QuotedTranslatedEndpoint']==383
assert positions['DiophantineConsistency.CurrentWitnessEquivalence2011']==512
assert positions['DiophantineConsistency.ObjectCurrentEquation2011']==529
print(json.dumps({'scope':'bounded read-only snapshot and historical endpoint evidence; no Lean, complete provider closure or raw document semantics',
 'retry_status':state['status'],'disk_floor_stop':True,'finished_stages':239,'planned_stages_remaining':290,
 'additional_final_audit_client':1,'next_stage':n,'archived_stage_logs_checked':len(outer['captured_logs']),
 'historical_quoted_endpoint_terminal_audit':history['status'],'historical_outer_session':48120},sort_keys=True,indent=2))
