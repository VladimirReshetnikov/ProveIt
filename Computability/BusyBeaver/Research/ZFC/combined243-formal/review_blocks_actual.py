#!/usr/bin/env python3
"""Independent read/hash review of existing records only; invokes no supplied tool."""
from pathlib import Path
import hashlib,json,re,collections
O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
load=lambda p:json.loads(Path(p).read_text())
for key,run,np,nc,nproj,guard in [('blocks','run1',14,14,3,'check.py')]:
 B=Path('/tmp/zfc243-combined-lean')/key; P=B/run/'verification.json'; r=load(P); checks=[]
 def check(x,s):
  assert x,(key,s)
  checks.append(s)
 check(r['status']=='PASS' and not r['prepare_only'],'terminal actual PASS')
 check((r['named_axiom_probes'],r['callers'],r['warnings'])==(np,nc,0),'census and zero warnings')
 check(r['before']==r['after'] and r['all_input_provider_postchecks'],'before/after exact')
 for p,h in r['before'].items():check(sha(p)==h,'current input '+p)
 for k in ['source','audit']:check(sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256'],k+' snapshot')
 check(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],'resource defaults')
 check(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'no version/build/download')
 check([c['label'] for c in r['commands']]==['source','audit'],'sequential source/audit')
 for i,c in enumerate(r['commands']):
  check(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'successful command '+str(i))
  check(Path(c['log']).read_text()==c['output'] and sha(c['log'])==c['log_sha256'],'raw log '+str(i))
  check(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'command flags/selection '+str(i))
  check('warning:' not in c['output'] and 'sorryAx' not in c['output'],'no warning/untrusted output '+str(i))
 check(sum(c['seconds'] for c in r['commands'])<120,'measured shared bound')
 check(r['source_object_recorded_before_audit'] and r['all_fresh_objects_unchanged_after_audit'],'fresh capture assertions')
 check(len(r['fresh_modules'])==1,'one fresh object');f=r['fresh_modules'][0]
 check(r['source_pass_object']==dict(f,source_command_index=0),'preaudit object descriptor')
 check(r['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'preaudit first provider descriptor')
 check(sha(f['path'])==f['sha256'] and f['source_sha256']==r['source']['sha256'],'fresh current bytes')
 check(r['commands'][0]['command'][-3:-1]==['-o',f['path']],'source output object')
 projects={q['module']:q for q in r['reused_modules']};seen=set();external={'Init'}
 def visit(m):
  if m not in projects:external.add(m);return
  if m in seen:return
  seen.add(m)
  for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):visit(n)
 for m in re.findall(r'^import\s+(\S+)\s*$',Path(r['source']['path']).read_text(),re.M):visit(m)
 check(seen==set(projects)==set(r['exact_project_import_closure']) and len(seen)==nproj,'exact project DFS')
 check(external=={q['module'] for q in r['toolchain_providers']},'exact tool boundary')
 for q in projects.values():
  for k in ['source','object']:check(sha(q[k])==q[k+'_sha256'],'provider '+k+' '+q['module'])
 roots=[Path(r['LEAN_PATH']),Path(r['compiler']['path']).parent.parent/'lib/lean']
 def first(m):return next((p/Path(m.replace('.','/')).with_suffix('.olean')).resolve() for p in roots if (p/Path(m.replace('.','/')).with_suffix('.olean')).is_file())
 for q in r['actual_first_providers']:check(first(q['module'])==Path(q['actual_first']).resolve() and sha(first(q['module']))==q['sha256'],'actual first '+q['module'])
 check(first(f['module'])==Path(f['path']).resolve(),'fresh target first')
 e=r['provider_evidence'][0];check(sha(e['path'])==e['sha256'],'parent pin');parent=load(e['path'])
 for ep in r['provider_evidence']:check(sha(ep['path'])==ep['sha256'],'all parent pins')
 for tq in r['toolchain_providers']:
  check(any(tq in load(ep['path'])['toolchain_providers'] for ep in r['provider_evidence']),'tool provenance '+tq['module'])
 for m,q in projects.items():
  old=next((z for z in parent['reused_modules'] if z['module']==m),None)
  if old:check(q==old,'exact inherited parent pair '+m)
  else:
   pf=next(z for z in parent['fresh_modules'] if z['module']==m)
   check((q['source'],q['source_sha256'],q['object'],q['object_sha256'])==(parent['source']['path'],parent['source']['sha256'],pf['path'],pf['sha256']),'fresh parent pair '+m)
   check(parent['source_pass_object']==dict(pf,source_command_index=0) and parent['fresh_first_provider_before_audit']=={k:pf[k] for k in ['module','path','sha256']},'parent captured before audit')
 audit=Path(r['audit']['path']).read_text();names=re.findall(r'^#print axioms (\S+)$',audit,re.M)
 raw=re.findall(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",r['commands'][1]['output'],re.M)
 parsed=[dict(name=n,axioms=sorted(a.strip() for a in ax.split(',') if a.strip())) for n,ax,no in raw]
 check([q['name'] for q in parsed]==names and len(names)==np,'all raw reports in audit order')
 check(parsed==r['axiom_reports'] and all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'} for q in parsed),'standard exact axiom sets')
 check(len(re.findall(r'^example\b',audit,re.M))==nc,'typed caller census')
 pre=B/'prepared1/verification.json';p=load(pre)
 check(p['status']=='PREPARED_NOT_BUILT' and p['prepare_only'] and p['commands']==p['fresh_modules']==[],'preparation remained unbuilt')
 check(p['before']==p['after'] and p['all_input_provider_postchecks'],'preparation stable')
 for path,h in p['before'].items():check(sha(path)==h,'prepared current '+path)
 history=[]
 if key=='table-rotation':
  oldguard=B/'check.py';newguard=B/'check-v2.py'
  check(oldguard.read_text().replace("require(not obj.exists(),'Target already exists.');run('source',ss,obj)","require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)")==newguard.read_text(),'exact mkdir-only guard repair')
  failure=B/'run1/verification.json';z=load(failure)
  check(z['status']=='FAIL' and [c['label'] for c in z['commands']]==['source'] and z['fresh_modules']==[],'first failed attempt no audit/fresh accepted')
  check(z['before']==z['after'] and z['all_input_provider_postchecks'],'failed attempt input postchecks')
  for path,h in z['before'].items():check(sha(path)==h,'failed attempt current '+path)
  c=z['commands'][0];check(c['exit_code']!=0 and not c['timed_out'] and c['interrupted'] is None,'output directory failure not timeout')
  check(Path(c['log']).read_text()==c['output'] and sha(c['log'])==c['log_sha256'] and 'failed to write' in c['output'] and 'failed to create file' in c['output'],'original raw failed output retained')
  check(z['source']['sha256']==r['source']['sha256'] and z['audit']['sha256']==r['audit']['sha256'],'source/audit unchanged across repair')
  history=[desc(failure),desc(oldguard),desc(B/'guard-output-directory-repair.json'),desc(B/'guard-output-directory-repair.diff')]
 result=dict(status='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS',findings=[],reviewer_role='Existing-evidence reviewer and author of this mechanical source/audit port and guard. Independent source/guard peer review is separately linked; root executed the proof, not this reviewer. This receipt is not an independent review of the implementation authored by this reviewer.',reviewer_source=desc(__file__),verification=desc(P),source=desc(r['source']['path']),audit=desc(r['audit']['path']),guard=desc(B/guard),boundary=desc(r['boundary']['path']),preparation=desc(pre),scope=r['scope'],counts=dict(inputs=len(r['before']),projects=nproj,probes=np,callers=nc,warnings=0),axiom_distribution={','.join(k) if k else 'empty':v for k,v in collections.Counter(tuple(q['axioms']) for q in parsed).items()},fresh_object=f,parent_scope=r['parent_scope'],scope_limit='Selected narrow provider closure and current evidence only. No broad ancestor replay, full Rotation244/Combined243 runtime or consistency calibration, or PA internalization claim.',history=history,source_review=desc(O/'independent-port-source-review.json'),supplied_execution=False,checks=checks,check_count=len(checks))
 out=O/(key+'-actual-evidence-review.json');out.write_text(json.dumps(result,indent=2)+'\n');print(desc(out),result['axiom_distribution'])
