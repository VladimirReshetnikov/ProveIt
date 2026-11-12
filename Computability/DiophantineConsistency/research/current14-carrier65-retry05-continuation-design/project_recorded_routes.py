#!/usr/bin/env python3
"""Pure projection of saved guard records; no output tree, subprocess or Lean."""
import hashlib,json,sys
from pathlib import Path
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
P=D/'research/current14-coherent-extension-refactor-retry05-runner'
F=D/'research/current14-carrier65-retry05-prefix-feasibility'
OLD=Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_text())
plan=read(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=read(P/'attempt01/state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
obs=read(F/'observation.json','4d5e69018251752909159818e193b8f64784f51c645941291facd1658b7e292b')
assert sha(F/'inspect.py')=='971d616f6216ad3f62ccf0a1084e1b6346a9e1c97e34072d76eb909556046349'
assert sha(P/'run.py')=='f025f9fdf7ec59762faab7d135bed4bff50fe841f08397c0d126f83236d3e84e'
assert sha(P/'monitor.py')=='5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0'
assert state['status']=='FAILED' and state['failure']=="Refusal('disk_floor')"
assert len(state['rows'])==240 and len(plan['entries'])==529
# Hypothetical map for a fresh lib root with base links and reused prefix
# symlinks. Paths are labels only: no directory or symlink is made here.
virtual={}
for raw,v in state['base_links'].items():
 p=Path(raw);assert p.is_relative_to(OLD) and raw.endswith('.olean')
 rel=str(p.relative_to(OLD));assert rel not in virtual
 virtual[rel]=v
assert len(virtual)==1000
for row in state['rows'][:239]:
 obj=OLD/(row['module'].replace('.','/')+'.olean')
 rel=str(obj.relative_to(OLD));assert rel not in virtual
 v=row['output_guard'][str(obj)]
 assert v is not None and v['sha256']==row['object_sha256'] and v['realpath']==str(obj)
 virtual[rel]=v
assert len(virtual)==1239
counts=Counter();logical={}
for row in state['rows'][:239]:
 for raw,v in row['direct_guard'].items():
  p=Path(raw)
  if p.is_relative_to(OLD):
   # A path under the future root is modeled by the old suffix. Its link
   # target would be the recorded original producer; absence is explicit.
   rel=str(p.relative_to(OLD));projected=virtual.get(rel)
   assert projected==v,(row['module'],raw,'hypothetical guard differs')
   label='@NEW_LIB@/'+rel;counts['new_root_guard_entries']+=1
  else:
   # This preserves recorded values only; it does not rehash external files.
   label=raw;projected=v;counts['unchanged_external_guard_entries']+=1
  if label in logical:assert logical[label]==projected,label
  else:logical[label]=projected
 for name,v in row['dependencies'].items():
  p=Path(v['path'])
  if p.is_relative_to(OLD):
   rel=str(p.relative_to(OLD));assert virtual[rel]=={'realpath':v['realpath'],'sha256':v['sha256']}
   counts['dependency_paths_relabelled']+=1
  else:counts['dependency_paths_unchanged']+=1
pending=plan['entries'][239:];assert len(pending)==290
for e in pending:
 assert e['module'].replace('.','/')+'.olean' not in virtual,e['module']
assert 'DiophantineConsistency/Current14CoherentAudit.olean' not in virtual
assert pending[0]['module']=='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert obs['stage240_recorded_children']==0 and obs['stage240_declared_project_import_producer_stage']==224
assert state['elapsed_seconds']==2487.332
print(json.dumps({'scope':'abstract saved-record path projection only; no filesystem materialization, Lean or safety certification',
 'virtual_base_olean_links':1000,'virtual_prefix_olean_links':239,
 'new_root_guard_entries_projected':counts['new_root_guard_entries'],
 'unchanged_external_guard_entries_recorded':counts['unchanged_external_guard_entries'],
 'unique_logical_guard_paths':len(logical),
 'dependency_paths_relabelled':counts['dependency_paths_relabelled'],
 'dependency_paths_unchanged':counts['dependency_paths_unchanged'],
 'pending_modules':len(pending),'separate_audit_client':1,
 'prior_attempt_elapsed_seconds':state['elapsed_seconds'],
 'stage240':pending[0]['module']},sort_keys=True,indent=2))
