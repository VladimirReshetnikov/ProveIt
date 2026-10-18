#!/usr/bin/env python3
"""Root publication of already passed runtime units; no proof execution."""
from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
RUN=Path('/tmp/zfc-rotation244-runtime-ports-v1')
PLAN=Path('/tmp/zfc-rotation244-runtime-plan/port-proposal')
OUT=Path('/tmp/zfc-rotation244-runtime-publication')
assert not OUT.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=RUN/'control/runtime-manifest.json'
assert sha(manifest)=='28c577e87e4c51d5740cfea2720c8a2ea41ff6777bc73eabca14bf955cdff438'
assert sha(RUN/'control/check_runtime.py')=='0c9cc3527dc255c8e23ffc543067e230c05365007dcda71266fa0f3daba28ee8'
m=json.loads(manifest.read_text());units=['kernel',*m['units']];data=[];checks=0
for name in units:
 p=RUN/name/'run1/verification.json';e=json.loads(p.read_text())
 assert e['status']=='PASS' and e['warnings']==0 and e['before']==e['after']
 assert e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms']
 for path,h in e['before'].items():assert sha(path)==h;checks+=1
 for role in ['source','audit']:
  for k in ['path','snapshot']:assert sha(e[role][k])==e[role]['sha256'];checks+=1
 assert [c['label']for c in e['commands']]==['source','audit']
 for c in e['commands']:
  assert c['exit_code']==0 and not c['timed_out'] and c['interrupted']is None
  assert Path(c['log']).read_text()==c['output'] and sha(c['log'])==c['log_sha256']
 assert (e['shared_timeout_seconds'],e['LEAN_NUM_THREADS'],e['memory_mebibytes'],e['global_option_overrides'])==(120,'1',4096,[])
 assert not e['dependency_build'] and not e['downloads'] and not e['compiler_version_query_performed']
 names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['path']).read_text(),re.M)
 rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",e['commands'][1]['output'],re.M)
 assert [n for n,_ in rr]==names and len(names)==e['named_axiom_probes']
 assert all({s.strip()for s in a.split(',')if s.strip()}<={'propext','Classical.choice','Quot.sound'}for _,a in rr)
 assert len(re.findall(r'^example\b',Path(e['audit']['path']).read_text(),re.M))==e['callers']
 f,=e['fresh_modules'];assert sha(f['path'])==f['sha256'] and f['source_sha256']==e['source']['sha256']
 assert e['source_object_recorded_before_audit'] and all(e['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256'])
 cap=e['fresh_first_provider_before_audit'];assert cap['module']==f['module'] and cap['sha256']==f['sha256'] and Path(cap['path']).resolve()==Path(f['path']).resolve()
 if name!='kernel':
  spec=m['units'][name];assert e['named_axiom_probes']==spec['probes'] and e['callers']==spec['callers']
  assert e['source']['sha256']==spec['source']['sha256']and e['audit']['sha256']==spec['audit']['sha256']
 else:assert(e['named_axiom_probes'],e['callers'])==(20,3)
 data.append((name,p,e))
assert sum(e['named_axiom_probes']for _,_,e in data)==106
assert sum(e['callers']for _,_,e in data)==94
blobs={};aliases=[];excluded=[];current={}
for root in [RUN,PLAN]:
 for p in sorted(root.rglob('*')):
  if p.is_symlink():excluded.append(dict(path=str(p),reason='symlink'));continue
  if not p.is_file():continue
  if p.suffix in ['.olean','.ilean','.c','.o','.so','.pyc']:
   excluded.append(dict(path=str(p),reason='compiled artifact'));continue
  raw=p.read_bytes()
  try:t=raw.decode('utf-8')
  except UnicodeDecodeError:excluded.append(dict(path=str(p),reason='non-UTF8'));continue
  h=hashlib.sha256(raw).hexdigest();blobs.setdefault(h,t);aliases.append(dict(path=str(p),sha256=h));current[str(p)]=h
OUT.mkdir();rows=[];relbase=Path('Computability/BusyBeaver/Research/ZFC');packet=relbase/'rotation244-runtime'
def add(dst,raw,original=None):
 target=ROOT/dst;assert not target.exists(),target
 src=OUT/'files'/str(len(rows))/target.name;src.parent.mkdir(parents=True);src.write_bytes(raw)
 rows.append(dict(source=str(src),destination=str(target),sha256=sha(src),bytes=len(raw),original=original))
def copy(dst,src):add(dst,Path(src).read_bytes(),str(src))
def js(dst,obj):add(dst,(json.dumps(obj,ensure_ascii=False,indent=2)+'\n').encode())
for name,p,e in data:
 module=e['fresh_modules'][0]['module'].split('.')[-1]
 copy(Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')/(module+'.lean'),e['source']['path'])
 copy(packet/'audits'/(module+'Audit.lean'),e['audit']['path'])
 copy(packet/'records'/(name+'-verification.json'),p)
 copy(packet/'records'/(name+'-prepared.json'),RUN/name/'prepared1/verification.json')
 for c in e['commands']:copy(packet/'logs'/(name+'-'+c['label']+'.log'),c['log'])
copy(relbase/'results/rotation244-runtime-verification.json',RUN/'runtime/run1/verification.json')
for name in ['runtime-manifest.json','check_runtime.py','run_remaining_root.py','freeze.json','SEQUENTIAL-PLAN.md']:
 copy(packet/'provenance'/name,RUN/'control'/name)
copy(packet/'provenance/build_packet_root.py',__file__)
js(packet/'history.json',dict(scope='Lossless UTF8 history from runtime-port and port-proposal roots; no compiled caches. Uncompiled drafts and emission failures remain historical.',aliases=aliases,blobs=blobs,excluded=excluded))
summary=dict(status='PUBLISH_EXISTING_NINE_RUNTIME_PASSES',units=[dict(unit=name,module=e['fresh_modules'][0]['module'],record=str(p),record_sha256=sha(p),probes=e['named_axiom_probes'],callers=e['callers'],seconds=sum(c['seconds']for c in e['commands']),projects=e['exact_project_prerequisite_count'])for name,p,e in data],probes=106,callers=94,warnings=0,current_input_checks=checks,history_aliases=len(aliases),history_blobs=len(blobs),proof_execution=False,simulation_execution=False,compiled_objects_published=False,limitations='Runtime equivalence requires Covered and Related. Exact tree coverage, bootstrap frame composition, closed binary endpoint and PA remain separate. Original guards retain historical scratch paths; no clean-checkout build claim.')
js(relbase/'results/rotation244-runtime-publication.json',summary)
for p,h in current.items():assert sha(p)==h
(OUT/'map.json').write_text(json.dumps(dict(files=rows),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),modules=len(data),probes=106,callers=94,map=str(OUT/'map.json'))))
