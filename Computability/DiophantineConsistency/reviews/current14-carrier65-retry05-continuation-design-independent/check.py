#!/usr/bin/env python3
"""Independent abstract record projection and bounded size observations; no Lean."""
from pathlib import Path
import ast,hashlib,json,sys
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];R=D/'research/current14-coherent-extension-refactor-retry05-runner';F=D/'research/current14-carrier65-retry05-continuation-design'
OLD=Path('/tmp/current14-coherent490-refactor-retry05-20261110/lib')
OUT=OLD.parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def pin(path,h):assert sha(path)==h,str(path);return json.loads(path.read_bytes())
plan=pin(R/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=pin(R/'attempt01/state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
projection=pin(F/'projection.json','48eb97ec3338a2b5702abb7f725d2a2f1df904240ef14322eada988603a36c8e')
assert sha(F/'project_recorded_routes.py')=='a561a384c42ebf24f8f7cbe810941cc3c041532d58abcf450d375de4ecfb7d9e'
assert state['status']=='FAILED' and state['failure']=="Refusal('disk_floor')"
assert len(state['rows'])==240 and len(plan['entries'])==529
assert state['elapsed_seconds']==2487.332
# Build the abstract source-to-target input map independently. No path under
# a new root is created. Prefix links point at old produced files; base links
# point at the recorded base object realpaths, and both retain recorded hashes.
virtual={};kind={}
for raw,entry in state['base_links'].items():
 path=Path(raw);rel=path.relative_to(OLD).as_posix()
 assert rel.endswith('.olean') and rel not in virtual
 virtual[rel]=(entry['realpath'],entry['sha256']);kind[rel]='base'
for row in state['rows'][:239]:
 rel=row['module'].replace('.','/')+'.olean';old=OLD/rel
 assert rel not in virtual
 entry=row['output_guard'][str(old)]
 assert entry is not None and entry['realpath']==str(old) and entry['sha256']==row['object_sha256']
 virtual[rel]=(entry['realpath'],entry['sha256']);kind[rel]='prefix'
assert Counter(kind.values())=={'base':1000,'prefix':239}
pending=[e['module'].replace('.','/')+'.olean' for e in plan['entries'][239:]]
assert len(pending)==len(set(pending))==290
assert not set(pending)&set(virtual)
assert 'DiophantineConsistency/Current14CoherentAudit.olean' not in virtual
assert plan['entries'][239]['module']=='DiophantineConsistency.Sign17KWeightAggregateProbe'
assert not set(state['rows'][239])&{'deps','compile','output_guard','object_sha256'}
# Reconstruct all recorded guards by independent counters and a consistency
# map; unchanged external guards are copied as records only, not rehashed.
count=Counter();logical={}
for row in state['rows'][:239]:
 for raw,v in row['direct_guard'].items():
  p=Path(raw)
  if p.is_relative_to(OLD):
   label='@NEW_LIB@/'+p.relative_to(OLD).as_posix(); t=virtual.get(p.relative_to(OLD).as_posix())
   actual=None if v is None else (v['realpath'],v['sha256'])
   assert actual==t
   count['new']+=1
  else:
   label=raw;actual=None if v is None else (v['realpath'],v['sha256']);count['external']+=1
  if label in logical: assert logical[label]==actual
  else:logical[label]=actual
 for dep,v in row['dependencies'].items():
  p=Path(v['path'])
  if p.is_relative_to(OLD):
   assert virtual[p.relative_to(OLD).as_posix()]==(v['realpath'],v['sha256']);count['relabeled']+=1
  else:count['unchanged']+=1
assert count=={'new':9308,'external':18616,'relabeled':373,'unchanged':343}
assert len(logical)==12090
for k,v in [('virtual_base_olean_links',1000),('virtual_prefix_olean_links',239),('new_root_guard_entries_projected',count['new']),('unchanged_external_guard_entries_recorded',count['external']),('unique_logical_guard_paths',len(logical)),('dependency_paths_relabelled',count['relabeled']),('dependency_paths_unchanged',count['unchanged']),('pending_modules',len(pending)),('separate_audit_client',1),('prior_attempt_elapsed_seconds',state['elapsed_seconds']),('stage240',plan['entries'][239]['module'])]: assert projection[k]==v,k
# Point-in-time sizes are observations of the old evidence only, not required
# capacity or evidence of closure/immutability. Links are followed for stat.
prefix_bytes=sum((OLD/(r['module'].replace('.','/')+'.olean')).stat().st_size for r in state['rows'][:239])
base_bytes=sum(Path(p).stat().st_size for p in state['base_links'])
source_bytes=sum((OUT/'src'/(e['module'].replace('.','/')+'.lean')).stat().st_size for e in plan['entries'])+(OUT/'src/DiophantineConsistency/Current14CoherentAudit.lean').stat().st_size
assert (prefix_bytes,base_bytes,source_bytes)==(147327432,449864896,2775906)
# The projection code's AST has no imports beyond its documented read-only
# helpers and no call to open/write/subprocess; this bounded check is not a
# general Python safety proof.
tree=ast.parse((F/'project_recorded_routes.py').read_text())
imports=[]
for node in ast.walk(tree):
 if isinstance(node,ast.Import):imports.extend(alias.name for alias in node.names)
 if isinstance(node,ast.ImportFrom):imports.append(node.module)
 if isinstance(node,ast.Call):
  if isinstance(node.func,ast.Name):assert node.func.id not in {'open','exec','eval','compile','__import__'}
  if isinstance(node.func,ast.Attribute):
   assert node.func.attr not in {'write_text','write_bytes','unlink','rename','mkdir','symlink_to','hardlink_to','touch','system','popen'}
   if node.func.attr=='replace':assert isinstance(node.func.value,ast.Subscript)
assert set(imports)<={'hashlib','json','sys','pathlib','collections'}
print(json.dumps({'scope':'independent abstract record projection and point-in-time size observation; no Lean, filesystem materialization or safety certification',
 'virtual_inputs':dict(Counter(kind.values())),'guard_entries':dict(count),'logical_guard_paths':len(logical),
 'pending_outputs':len(pending),'separate_audit_output':1,'prior_elapsed_seconds':state['elapsed_seconds'],
 'prefix_bytes':prefix_bytes,'base_bytes':base_bytes,'source_bytes':source_bytes},sort_keys=True,indent=2))
