"""Existing root-execution evidence review. No guard, generator or compiler calls."""
from pathlib import Path
import hashlib,json,os,re
B=Path('/tmp/zfc-routing245-lean/coverage-production/v4');cache={};icache={};checks=0

def chk(v,s):
 global checks
 assert v,s
 checks+=1
def sha(p):
 p=str(Path(p).resolve())
 if p not in cache:cache[p]=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 return cache[p]
def desc(p):return dict(path=str(p),sha256=sha(p))
def imports(p):
 p=str(Path(p).resolve())
 if p in icache:return icache[p]
 t=Path(p).read_text();out=[];i=d=0
 while i<len(t):
  z=t[i:i+2]
  if z=='/-':d+=1;i+=2
  elif d and z=='-/':d-=1;i+=2
  elif d:i+=1
  elif z=='--':
   j=t.find('\n',i);i=len(t)if j<0 else j
  else:out.append(t[i]);i+=1
 chk(d==0,'comments');icache[p]=[n for m in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)',''.join(out),re.M)for n in m[1].split()];return icache[p]
M=B/'sources/generation.json';manifest=json.loads(M.read_text());G=B/'check-production-v4.py'
chk(sha(M)=='b79fe539f343ca2f8979ada70f534f2ee08fb2361598a87f39c1e410fe6c32bc','manifest')
chk(sha(G)=='c37473de1eacb7a47a397e49bbff9b0bed9eeb1efbebea21f3c0835ecf42f7b5','guard')
batches=[('batch264-run1','b4fd96989338eaa39dbeccc9e2add36903c4106ccd6f5676d2f37c987eb45d36',196)]
summary=[];allrecords=[];totalrefs=0
for name,pin,start in batches:
 bp=B/name/'batch.json';b=json.loads(bp.read_text());rrp=B/name/'root-review.json';rr=json.loads(rrp.read_text())
 chk(sha(rrp)=='1d65d128771014c42c86cb383878e97cf2a5b5bb20f895da8427106aad671645','root receipt pin')
 chk(sha(bp)==pin and b['status']=='PASS_SELECTED_UNITS'and b['selected_unit_indices']==list(range(start,start+72))and len(b['completed_units'])==72,'terminal selected batch')
 chk(b['guard']['sha256']==sha(G)and b['manifest']['sha256']==sha(M)and b['serial']and not b['prepare_only'],'batch binding')
 chk(not b['compiler_version_query_performed']and not b['dependency_build']and not b['downloads'],'no auxiliary execution')
 rows=[];probes=callers=refs=0;times=[];inputpaths=set()
 for i,q in zip(range(start,start+72),b['completed_units']):
  ep=Path(q['record']['path']);e=json.loads(ep.read_text());pp=Path(q['preparation']['path']);p=json.loads(pp.read_text());u=manifest['units'][i]
  chk(sha(ep)==q['record']['sha256']and sha(pp)==q['preparation']['sha256']and e['preparation']==q['preparation'],'selected record and preparation')
  chk(e['status']=='PASS'and not e['prepare_only']and q['unit_index']==i==e['unit_index']==p['unit_index']and q['module']==e['module']==u['module'],'actual unit identity')
  chk(e['unit_kind']==u['kind']and e['guard_cases']==u['guards']and e['cuts']==u['cuts'],'actual manifest semantics')
  chk(p['status']=='PREPARED_NOT_BUILT'and p['prepare_only']and p['commands']==[]and p['fresh_modules']==[],'prepared gate')
  chk(e['before']==p['before']and e['reused_modules']==p['reused_modules']and e['actual_first_providers']==p['actual_first_providers'],'preparation selects actual inputs/providers')
  for r in [p,e]:
   chk(r['before']==r['after']and r['all_input_provider_postchecks'],'postcheck stability')
   for path,h in r['before'].items():chk(sha(path)==h,'current before/after '+path);totalrefs+=1
   chk(not r['compiler_version_query_performed']and not r['source_overridden']and not r['audit_overridden']and not r['dependency_build']and not r['downloads'],'no overrides or auxiliary execution')
   chk(r['site_fuel']==4000 and r['margin']==64 and r['shared_wall_seconds']==120 and r['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),'unchanged bounds')
   for role in ['source','audit']:
    z=r[role];chk(sha(z['path'])==sha(z['snapshot'])==z['sha256']==u[role+'_sha256']and Path(z['path'])==M.parent/u[role],'exact source/audit '+role)
  refs+=len(e['before']);inputpaths.update(e['before'])
  chk(imports(e['source']['path'])==u['imports'],'reviewed exact source imports')
  pool={z['module']:z for z in e['reused_modules']};tools={z['module']:z for z in e['toolchain_providers']};actual={z['module']:z for z in e['actual_first_providers']}
  chk(len(pool)==e['project_module_count']and e['exact_project_import_closure']and not e['external_project_boundaries']and set(actual)==set(pool),'actual project boundary')
  roots=[Path(z)for z in e['LEAN_PATH'].split(os.pathsep)]+[Path(e['compiler']['path']).parent.parent/'lib/lean']
  def first(m):
   rel=Path(m.replace('.','/')).with_suffix('.olean');return next(z/rel for z in roots if(z/rel).is_file())
  for m,z in pool.items():
   a=actual[m];chk(sha(z['source'])==z['source_sha256']and sha(z['object'])==z['object_sha256']and first(m).resolve()==Path(a['actual_first']).resolve()==Path(z['object']).resolve()and sha(first(m))==a['sha256']==z['object_sha256'],'selected provider '+m)
  for m,z in tools.items():chk(first(m).resolve()==Path(z['actual_first']).resolve()==Path(z['object']).resolve()==(Path(e['compiler']['path']).parent.parent/'lib/lean'/Path(m.replace('.','/')).with_suffix('.olean')).resolve()and sha(first(m))==z['object_sha256'],'toolchain provider')
  seen=set()
  def visit(m):
   if m in seen:return
   chk(m in pool,'selected import '+m);seen.add(m)
   for n in imports(pool[m]['source']):
    if n in pool:visit(n)
    else:chk(n in tools,'explicit tool import '+n)
  for m in u['imports']:visit(m)
  chk(seen==set(pool),'exact import DFS')
  chk([z['label']for z in e['commands']]==['source','audit']and e['source_object_recorded_before_audit']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'accepted ordered source/audit')
  for z in e['commands']:
   chk(z['exit_code']==0 and not z['timed_out']and not z['interrupted']and z['command'][1:3]==['-j1','-M4096'],'successful bounded command')
   chk(Path(z['log']).read_text()==z['output']and 'error:'not in z['output']and 'warning:'not in z['output']and 'sorryAx'not in z['output'],'raw log exact')
  chk(e['commands'][0]['output']==''and e['warnings']==dict(source=0,audit=0),'no warnings')
  f,=e['fresh_modules'];s=e['source_pass_object'];fp=e['fresh_first_provider_before_audit']
  chk(all(s[k]==f[k]for k in ['module','path','sha256','source_sha256'])and s['source_command_index']==0,'source capture before audit')
  chk(f['module']==u['module']and f['source_sha256']==u['source_sha256']and f['sha256']==sha(f['path'])==fp['sha256']and first(f['module']).resolve()==Path(fp['actual_first']).resolve()==Path(f['path']).resolve()and not Path(f['path']).is_symlink(),'fresh first provider')
  audit=Path(e['audit']['snapshot']).read_text();reported=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",e['commands'][1]['output'],re.S)
  sets=[dict(name=n,axioms=[x.strip()for x in a.split(',')if x.strip()])for n,a in reported]
  chk(sets==e['actual_axiom_sets']and [n for n,a in reported]==re.findall(r'^#print axioms (\S+)$',audit,re.M),'raw named axiom reports')
  chk(all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'}for z in sets),'standard axioms only')
  chk(len(sets)==e['named_axiom_probes']==e['expected_named_axiom_probes']==u['probes']and len(re.findall(r'^example\b',audit,re.M))==e['callers']==e['expected_callers']==u['callers'],'compiled audit census')
  elapsed=sum(z['seconds']for z in e['commands']);chk(elapsed<120,'actual shared duration');times.append(elapsed);probes+=e['named_axiom_probes'];callers+=e['callers'];rows.append(dict(index=i,module=u['module'],record=desc(ep),preparation=desc(pp),fresh_module=f,probes=e['named_axiom_probes'],callers=e['callers'],projects=e['project_module_count'],input_count=len(e['before']),shared_seconds=elapsed))
 chk(rr['batch']==desc(bp)and rr['unit_indices']==list(range(start,start+72))and rr['named_axiom_probes']==probes and rr['callers']==callers and rr['input_hash_references_checked']==refs and rr['unique_input_paths_checked']==len(inputpaths),'root receipt totals agree')
 summary.append(dict(batch=desc(bp),root_review=desc(rrp),indices=list(range(start,start+72)),unit_count=72,probes=probes,callers=callers,input_references=refs,unique_input_paths=len(inputpaths),max_shared_seconds=max(times),total_shared_seconds=sum(times),records=rows));allrecords.extend(rows)
report=dict(status='EXISTING_SELECTED_COVERAGE_BATCHES_REVIEW_PASS',findings=[],manifest=desc(M),guard=desc(G),reviewer_source=desc(Path(__file__)),batches=summary,unit_count=len(allrecords),probes=sum(q['probes']for q in summary),callers=sum(q['callers']for q in summary),current_preparation_and_actual_input_references=totalrefs,distinct_rehashed_paths=len(cache),checks=checks,scope='Only existing terminal selected batch264: actual unit indices196..267,72 modules. All preparation gates, recorded before/after/current bytes, source/audit snapshots, exact provider DFS/first objects, fresh capture before audit, successful bounded raw commands and named standard-axiom reports independently checked. The frozen manifest is the prior reviewed complete-family plan; no claim that the full family has passed or that final routing245 binary coverage is established.',reviewer_role='This reviewer authored the production source/guard family; this receipt independently checks root-executed records and root summaries, and does not claim independent authorship review of the generator or guard.',warnings=0,reader_development='Predecessor reader already incorporated three schema corrections: coverage limits include shared_wall_seconds, tool providers have no duplicate toolchain_reference_sha256 key, and axiom reports use name rather than theorem. No evidence mismatch or proof rerun occurred.',compiler_guard_generator_checker_execution_by_reviewer=False,maintained_edits=False)
out=B/'independent-batch264-actual-review.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(review=desc(out),units=report['unit_count'],probes=report['probes'],callers=report['callers'],refs=totalrefs,checks=checks)))
