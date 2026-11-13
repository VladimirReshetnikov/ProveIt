#!/usr/bin/env python3
"""Bounded independent retry05/historical endpoint audit. No Lean or mutations."""
from pathlib import Path
import hashlib, json, os, re, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
R=D/'research/current14-coherent-extension-refactor-retry05-runner'
A=R/'attempt01'; L=Path('/tmp/current14-coherent490-refactor-retry05-20261110')
Q=D/'research/current14-quoted-translated-endpoint-check/attempt01'
AUD=D/'research/current14-carrier65-retry05-resumption-audit'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for data in iter(lambda:f.read(1024*1024), b''): h.update(data)
 return h.hexdigest()
def pin(p,h):
 assert sha(p)==h, str(p)
 return p.read_text()
pin(AUD/'check.py','fb4e0ab1b3a96fc15ea3570f779b0a3bc7cfb7e2e10d998387a8d72b2f436f24')
claim=json.loads(pin(AUD/'result.json','4e443fc2d56543212bd8f6f7d90955a676f1caa4dfa21118b70b5008c8f9dc51'))
plan=json.loads(pin(R/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c'))
state=json.loads(pin(A/'state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82'))
outer=json.loads(pin(A/'outer-result.json','11e4abc49bceea5a05faaab13d56a1dacdebe4ec5c4b32742633288b657df4a7'))
runner=pin(R/'run.py','f025f9fdf7ec59762faab7d135bed4bff50fe841f08397c0d126f83236d3e84e')
assert sha(L/'state.json') == sha(A/'state.json')
assert state['status']==outer['status']=='FAILED' and state['failure']==outer['failure']=="Refusal('disk_floor')"
entries=plan['entries']; rows=state['rows']; assert len(entries)==529 and len(rows)==240
assert len(outer['captured_logs'])==478
compile_floor=[]
for index in range(239):
 e,r=entries[index],rows[index]
 assert r['module']==e['module'] and r['source_sha256']==e['source_sha256']
 obj=L/'lib'/(r['module'].replace('.','/')+'.olean')
 assert obj.is_file() and sha(obj)==r['object_sha256']
 for kind in ('deps','compile'):
  x=r[kind]; name=Path(x['log']).name
  assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids']
  assert sha(A/'logs'/name)==x['log_sha256']==outer['captured_logs'][name]
 compile_floor.append(r['compile']['min_disk_free_bytes'])
assert min(compile_floor)==5104041984
last=rows[-1]; target='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert entries[239]['module']==last['module']==target and all(k not in last for k in ('deps','compile','object_sha256'))
assert not (L/'lib'/(target.replace('.','/')+'.olean')).exists()
assert not list((L/'logs').glob('239-*'))
# Source inspection is bounded: observe the run entry uses default-fresh preflight,
# creates new owned state, snapshots sources, and initializes an empty stage map.
assert L.exists()
assert f"OUT=Path('{L}')" in runner
for text in ('def preflight(require_fresh=True):',"if require_fresh:need(not os.path.lexists(OUT),'output already exists')",'state=create_owned_state(OUT)','completed={};roots=', 'for index,e in enumerate(entries):',"need(len(completed)==530"):
 assert text in runner, text
for name,position in [('DiophantineConsistency.Current14QuotedTranslatedEndpoint',383),('DiophantineConsistency.CurrentWitnessEquivalence2011',512),('DiophantineConsistency.ObjectCurrentEquation2011',529)]:
 assert entries[position-1]['module']==name
qstate=json.loads(pin(Q/'state.json','65b86435269571d8b9e1439e45dd56cd8605939823d9e7e25ead6c8c8a90815b'))
qouter=json.loads((Q/'outer-result.json').read_text()); assert qstate['status']=='PASS' and qouter['outer_session']==48120 and qouter['outer_exit_code']==0 and qouter['state_sha256']==sha(Q/'state.json')
log=' '.join(pin(Q/'Current14QuotedTranslatedEndpoint-compile.txt','4f3e8dbde2a08381dec7174fa7825a333715bd7dde8fb58d622f7b43d16054c3').split())
assert 'quoted_translated_endpoint' in log and '[propext, Classical.choice, Quot.sound]' in log and not any(x in log for x in ('error:','warning:','sorryAx'))
ep=pin(D/'research/current14-quoted-translated-endpoint-draft/Current14QuotedTranslatedEndpoint.lean','90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965')
assert '∃ φ, quoteSentence = some φ' in ep and 'standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ' in ep
source=(D/'Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean').read_text()
assert 'def sourceSentence : ArithmeticSentence :=' in source and 'ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent' in source
assert claim['finished_stages']==239 and claim['planned_stages_remaining']==290 and claim['archived_stage_logs_checked']==478
print(json.dumps({'scope':'bounded independent source, record and artifact observations; no Lean replay or physical-document semantics', 'completed_stages':239,'remaining_stages_excluding_audit_client':290,'archived_child_logs':478,'minimum_recorded_compile_disk_bytes':min(compile_floor),'next_stub':target,'retained_runner_is_fresh_output_only':True,'historic_endpoint_compile_log_axioms':['propext','Classical.choice','Quot.sound'],'historic_endpoint_scope':'standard-iPRA normalized quoted sentence versus mapped GG Foundation ZFC consistency'},sort_keys=True,indent=2))
