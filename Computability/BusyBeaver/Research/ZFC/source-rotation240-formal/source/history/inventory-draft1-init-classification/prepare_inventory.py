#!/usr/bin/env python3
"""Own static source/provider inventory; no imports or execution of proof tools."""
from pathlib import Path
import hashlib, json, re

B=Path(__file__).parent
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=Path('/tmp/zfc243-source-bridge/run2/verification.json')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p): return {'path':str(p),'sha256':sha(p)}
checks=0
def ck(x,label):
 global checks
 checks+=1
 if not x: raise AssertionError(label)

ck(sha(P)=='cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701','actual parent identity')
parent=json.loads(P.read_text())
ck(parent['status']=='PASS' and not parent['prepare_only'],'actual successful parent')
ck(parent['named_axiom_probes']==9 and parent['callers']==10 and parent['warnings']==0,'parent census')
ck(parent['source_object_recorded_before_audit'] and parent['fresh_first_provider_before_audit'],'parent fresh capture')
providers=list(parent['reused_modules'])+[{'module':'BusyBeaver.ZFC.SourceRotation244','source':parent['source']['path'],'source_sha256':parent['source']['sha256'],'object':parent['source_pass_object']['path'],'object_sha256':parent['source_pass_object']['sha256']}]
lookup={p['module']:p for p in providers}
ck(len(lookup)==len(providers)==9,'nine projects')
for p in providers:
 ck(sha(p['source'])==p['source_sha256'],('source identity',p['module']))
 ck(sha(p['object'])==p['object_sha256'],('object identity',p['module']))
 ck(sha(R/'Computability/BusyBeaver/Lean'/Path(p['module'].replace('.','/')).with_suffix('.lean'))==p['source_sha256'],('maintained source identity',p['module']))
seen=set(); external=set()
def walk(m):
 if m in seen:return
 ck(m in lookup,('closure source',m));seen.add(m)
 for line in Path(lookup[m]['source']).read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():
    if child.startswith('BusyBeaver.'):walk(child)
    else:external.add(child)
walk('BusyBeaver.ZFC.SourceRotation244')
ck(seen==set(lookup) and not external,'exact DFS no external project modules')
ck([p['module'] for p in parent['toolchain_providers']]==['Init'],'Init only')
for p in parent['toolchain_providers']:ck(sha(p['object'])==p['object_sha256'],'tool identity')
ck(sha(parent['compiler']['path'])==parent['compiler']['sha256'],'compiler identity')
for c in parent['commands']:
 ck(c['exit_code']==0 and not c['timed_out'],'parent actual command success')
 ck(sha(c['log'])==c['log_sha256'] and Path(c['log']).read_text()==c['output'],'parent raw output')

program_path=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean'
rows={}
for m in re.finditer(r'^private def row(\d+) : Row := (.+)$',program_path.read_text(),re.M):
 es=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',m[2])
 ck(len(es)==2,'two literal edges')
 rows[int(m[1])]=tuple((op,int(k) if k else 0) for op,k in es)
ck(set(rows)==set(range(203)),'complete literal DAG')
rows[5]=(('decnz',6),('cont',2));rows[6]=(('inc',0),('node',5));rows[169]=(('inc',5),('node',5))
bb={n:int(n in {0,9,173,174,175,184,185,191,192,194,195}) for n in rows}
cc={n:2 if n in {1,13,32} else int(n in {2,4,5,10,14,16,19,22,26,28,33,35,40,44,54,168,170}) for n in rows}
hh={n:n+1 for n in rows}
def eb(e):
 op,k=e
 return bb[k] if op=='node' else 1 if op=='decnz' else k if op=='brk' else 0
def ec(e):
 op,k=e
 return cc[k] if op=='node' else k if op=='cont' else 0
for n,(l,r) in rows.items():
 for op,k in (l,r):
  ck(op!='node' or 0<=k<203,'child node bounds')
  ck(op not in ('brk','cont') or k>0,'positive break/continue')
  ck((hh[k] if op=='node' else 0)<hh[n],'height inequality')
 ck(eb(l)<=bb[n]+1 and eb(r)<=bb[n],'break inequalities')
 ck(ec(l)<=cc[n] and ec(r)<=cc[n]+1,'continue inequalities')
ck(hh[202]<=204 and bb[202]==cc[202]==0,'root finite bounds')
leaves=[]
def unfold(e,p):
 op,k=e
 if op=='node':
  l,r=rows[k];unfold(l,p+'0');unfold(r,p+'1')
 else:leaves.append([p,{'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}[op],None if op=='halt' else k])
unfold(('node',202),'')
delivered=Path('/tmp/zfc-intake-e5c2b3337e/zfc240-source-rotation-20261018/machines/sites_logical.json')
ck(leaves==json.loads(delivered.read_text()),'exact ordered6455 delivered leaf list')
source=(B/'SourceRotation240.lean').read_text();audit=(B/'Audit.lean').read_text()
ck(source.count('import ')==1 and source.startswith('import BusyBeaver.ZFC.SourceRotation244\n'),'single direct import')
ck('if n = 169 then (.inc 5, .node 5)' in source,'exact row override')
ck(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source),'no proof admission or native oracle')
ck(not re.search(r'maxRecDepth|maxHeartbeats',source+audit),'default proof limits')
names=re.findall(r'^#print axioms (\S+)$',audit,re.M)
ck(len(names)==len(set(names))==10 and len(re.findall(r'^example\b',audit,re.M))==13,'10 probes13 callers')
plan={'status':'SOURCE_ONLY_UNCOMPILED_PROVIDER_PLAN','parent':desc(P),'parent_module':'BusyBeaver.ZFC.SourceRotation244','providers':providers,'project_count':9,'toolchain_providers':parent['toolchain_providers'],'compiler':parent['compiler'],'probe_names':names,'probes':10,'callers':13,'limits':{'shared_source_audit_seconds':120,'threads':1,'memory_mib':4096,'global_option_overrides':[],'dependency_build':False,'version_query':False},'guard_emitted':False,'proof_execution':False,'modern_parent_capture_required':True,'historical_parent_failure':'SourceRotation244 run1 source failed on definitional unfolding; exact one-line source-v2 repair and successful run2 remain distinct.','scope':'Arbitrary-register source equivalence only; no binary runtime/bootstrap or PA endpoint.'}
(B/'provider-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
inventory={'status':'SOURCE_ONLY_UNCOMPILED','source':desc(B/'SourceRotation240.lean'),'audit':desc(B/'Audit.lean'),'plan':desc(B/'plan.md'),'provider_plan':desc(B/'provider-plan.json'),'reviewer_source':desc(Path(__file__)),'delivered_leaves':desc(delivered),'static_checks':checks,'new_node_override':169,'exact_leaf_count':len(leaves),'guard_cases':sum(2 if op=='CD' else 1 for _,op,_ in leaves),'project_count':9,'probes':10,'callers':13,'own_static_only':True,'proof_compiler_executed':False,'source_guard_executed':False,'maintained_edits':False}
(B/'source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
print(json.dumps({'inventory':desc(B/'source-inventory.json'),'source':desc(B/'SourceRotation240.lean'),'audit':desc(B/'Audit.lean'),'checks':checks}))
