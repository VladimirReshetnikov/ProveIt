#!/usr/bin/env python3
"""Independent read/hash review of existing records only; invokes no supplied tool."""
from pathlib import Path
import hashlib,json,re,collections
O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
load=lambda p:json.loads(Path(p).read_text())
for key,np,nc,nproj in [('simulation',4,4,7)]:
 B=Path('/tmp/zfc244-compensated-lean')/key; P=B/'run1/verification.json'; r=load(P); checks=[]
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
 pool={}
 for e in r['provider_evidence']:
  check(sha(e['path'])==e['sha256'],'parent pin '+e['module']);parent=load(e['path'])
  check(parent['status']=='PASS' and parent['before']==parent['after'] and parent['all_input_provider_postchecks'],'parent complete '+e['module'])
  for path,h in parent['before'].items():check(sha(path)==h,'parent current '+path)
  pf=parent['fresh_modules'][0]
  check(parent['source_pass_object']==dict(pf,source_command_index=0) and parent['fresh_first_provider_before_audit']=={k:pf[k] for k in ['module','path','sha256']},'parent preaudit capture '+e['module'])
  rows=parent['reused_modules']+[dict(module=pf['module'],source=parent['source']['path'],source_sha256=pf['source_sha256'],object=pf['path'],object_sha256=pf['sha256'])]
  for q in rows:
   row={k:q[k] for k in ['module','source','source_sha256','object','object_sha256']}
   check(q['module'] not in pool or pool[q['module']]==row,'shared provider compatibility '+q['module'])
   pool[q['module']]=row
 check(pool==projects,'exact three-parent union')
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
 result=dict(status='EXISTING_ACTUAL_EVIDENCE_AND_GUARD_REVIEW_PASS',findings=[],reviewer_role='Independent assembly source/API and guard/evidence reviewer; author of the separate invariant prerequisite, not this source, audit, guard or execution.',reviewer_source=desc(__file__),verification=desc(P),source=desc(r['source']['path']),audit=desc(r['audit']['path']),guard=desc(B/'check.py'),boundary=desc(r['boundary']['path']),preparation=desc(pre),scope=r['scope'],counts=dict(inputs=len(r['before']),projects=nproj,probes=np,callers=nc,warnings=0),axiom_distribution={','.join(k) if k else 'empty':v for k,v in collections.Counter(tuple(q['axioms']) for q in parsed).items()},fresh_object=f,parent_scope=r['parent_scope'],scope_limit='Exact global244/245 halting equivalence for arbitrary Core finite-support tapes at old95 and blank. This review does not claim the later consistency endpoint or internal PA derivation; no broad851-provider ancestor replay.',supplied_execution=False,checks=checks,check_count=len(checks))
 out=O/(key+'-actual-review.json');out.write_text(json.dumps(result,indent=2)+'\n');print(desc(out),result['axiom_distribution'])
