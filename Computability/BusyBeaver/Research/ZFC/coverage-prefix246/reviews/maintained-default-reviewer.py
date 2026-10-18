#!/usr/bin/env python3
"""Read-only review of already completed maintained-default preparation.
No supplied checker/coordinator, compiler or version command is invoked.
"""
from pathlib import Path
import argparse,ast,collections,difflib,hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=R/'Computability/BusyBeaver/Research/ZFC'
W=Path('/tmp/zfc-prefix246-sites-maintained-prepare')
MANIFEST_SHA='8775c4e62aa3e7e8f80dcbf1971718b3a34cfdead8ad66eba812a486b75120c6'
COORD_SHA='7bf3fa743c78464324deb25f50efa38a7c6e634663a5e851a4e4cf466eac381b'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,s):
 if not b:raise ValueError(s)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();O=a.output.resolve();need(not O.exists()and not O.is_relative_to(R)and not O.is_relative_to(W),'Use new external review output')
 checks=0;paths={};resolved={};targets={}
 def bind(p,h):
  nonlocal checks
  p=Path(p).absolute();k=str(p);t=str(p.resolve());checks+=1
  if k in paths:need(paths[k]==h and targets[k]==t,'Path changed '+k)
  else:paths[k]=h;targets[k]=t
  if t in resolved:need(resolved[t]==h,'Conflicting target identity '+t)
  else:need(sha(p)==h,'Changed input '+k);resolved[t]=h
  return p
 def load(p,h=None):
  if h is not None:bind(p,h)
  return json.loads(Path(p).read_text())
 mp=Z/'coverage-prefix246/manifest.json';m=load(mp,MANIFEST_SHA);cpath=W/'coordination.json';c=load(cpath);ch=sha(cpath);bind(cpath,ch)
 need(c['status']=='PREPARED_NOT_BUILT'and c['prepare_only']and not c['stage_only']and c['compiler_invoked']is False,'Complete preparation gate')
 need(c['guard_preparations']==102 and len(c['commands'])==len(c['units'])==len(m['units'])==102,'102 Python preparations')
 need(not c['compiler_version_query_performed']and not c['dependency_build'],'No coordinator query/build')
 need(c['manifest']=={'path':str(mp),'sha256':MANIFEST_SHA}and c['coordinator_sha256']==COORD_SHA,'Installed manifest/coordinator pin')
 bind(Z/'check_prefix246_sites.py',COORD_SHA)
 def published(b):return bind(R/b['path'],b['sha256'])
 for h,row in m['content_registry'].items():
  for p in row['published_paths']:bind(R/p,h)
 site=published(m['site_parent']);by={u['module']:u for u in m['units']};portable=load(c['portable_manifest']['path'],c['portable_manifest']['sha256']);raw=load(published(m['plans']['pipeline']))
 need(portable['plan']==str(published(m['plans']['generation']))and portable['site_evidence']==str(site),'Portable installed parent paths')
 need([u['module']for u in portable['units']]==[u['module']for u in m['units']],'Portable unit ordering')
 results=[];global_providers={};proof_commands=0;fresh=0;direct_parent_count=0
 for unit,note,cmd,pu,ru in zip(m['units'],c['units'],c['commands'],portable['units'],raw['units']):
  module=unit['module'];need(module==note['module']==cmd['module']==pu['module']==ru['module'],'Unit correspondence')
  source=published(unit['artifacts']['source']);audit=published(unit['artifacts']['audit']);guard=published(unit['artifacts']['planned_guard']);staged=bind(note['staged_guard'],note['staged_guard_sha256']);delta=bind(note['defaults_only_diff'],note['defaults_only_diff_sha256'])
  original=guard.read_text();expected=original
  for old,new in [(unit['planned_source_path'],str(source)),(unit['planned_audit_path'],str(audit))]:
   needle='Path('+repr(old)+')';need(expected.count(needle)==1,'One default source/audit path');expected=expected.replace(needle,'Path('+repr(new)+')')
  need(staged.read_text()==expected,'Exact defaults-only guard bytes');ast.parse(expected)
  need(delta.read_text()==''.join(difflib.unified_diff(original.splitlines(True),expected.splitlines(True),fromfile=str(guard),tofile=str(staged))),'Exact defaults-only diff')
  expected_unit=dict(ru,source_path=str(source),audit_path=str(audit),guard=str(staged),guard_sha256=sha(staged));need(pu==expected_unit,'Portable manifest unit only path adaptations')
  need(note['source_sha256']==unit['artifacts']['source']['sha256']and note['audit_sha256']==unit['artifacts']['audit']['sha256']and note['raw_guard_sha256']==unit['artifacts']['planned_guard']['sha256'],'Coordinated source/audit/guard pins')
  vp=bind(note['preparation']['path'],note['preparation']['sha256']);d=load(vp);argv=cmd['command']
  need(cmd['exit_code']==0 and argv[1:3]==['-B',str(staged)]and '--prepare-only'in argv,'Actual Python-only preparation command')
  need(Path(argv[0]).name.startswith('python')and '--source'not in argv and '--audit'not in argv,'No compiler or source/audit override in command')
  for flag,val in [('--repo',str(R)),('--site-evidence',str(site)),('--output',str(vp.parent))]:need(argv[argv.index(flag)+1]==val,'Exact installed/default command '+flag)
  bind(cmd['log'],cmd['log_sha256'])
  deps=unit['generated_direct_dependencies']
  if deps:
   need('--dependencies'in argv,'Generated parent metadata');dp=Path(argv[argv.index('--dependencies')+1]);expected_deps={n:{'path':str(published(by[n]['artifacts']['verification'])),'sha256':by[n]['artifacts']['verification']['sha256']}for n in deps};need(load(dp)==expected_deps,'Installed exact direct parent records');direct_parent_count+=len(deps)
  else:need('--dependencies'not in argv,'Unexpected generated parent override')
  need(d['status']=='PREPARED_NOT_BUILT'and d['prepare_only']and d['commands']==[]and d['fresh_modules']==[],'No proof/fresh output')
  proof_commands+=len(d['commands']);fresh+=len(d['fresh_modules'])
  need(not d['source_overridden']and not d['audit_overridden']and not d['dependency_build']and not d['downloads']and not d['compiler']['compiler_version_query_performed'],'No override/build/download/version')
  need(d['source']['path']==str(source)and d['audit']['path']==str(audit),'Installed maintained defaults')
  for key,p in [('source',source),('audit',audit)]:need(d[key]['sha256']==sha(p),'Default proof bytes');bind(d[key]['snapshot'],d[key]['sha256'])
  need(d['before']==d['after']and d['all_input_provider_postchecks'],'All preparation input postchecks')
  for p,h in d['before'].items():bind(p,h)
  need(d['before'][str(staged)]==note['staged_guard_sha256'],'Actual staged guard binding')
  for p in d['provider_evidence']:bind(p['path'],p['sha256'])
  evidence_paths={p['path']for p in d['provider_evidence']};need(str(site)in evidence_paths,'Installed Site evidence bound')
  ps=d['parent_summaries'];actual_direct={p['module']:p for p in ps if p['label']=='generated_direct_dependency'};need(set(actual_direct)==set(deps),'Every exact generated direct parent bound')
  for n,row in actual_direct.items():need(row['evidence']==str(R/by[n]['artifacts']['verification']['path']),'Installed generated parent evidence path')
  prior=load(published(unit['artifacts']['verification']));need(d['compiler']==prior['compiler'],'Unchanged compiler identity')
  providers={p['module']:p for p in d['reused_modules']};prior_providers={p['module']:p for p in prior['reused_modules']}
  need(len(providers)==d['project_module_count']==unit['expected_provider_count']and set(providers)==set(prior_providers),'Exact prepared provider census')
  need(d['exact_project_import_closure']is True and d['external_project_boundaries']==[],'No hidden project boundary')
  for n,p in providers.items():
   pp=prior_providers[n];identity=(p['source_sha256'],p['object_sha256']);need(identity==(pp['source_sha256'],pp['object_sha256']),'Exact proof-run provider bytes retained')
   if n in global_providers:need(global_providers[n]==identity,'Cross-unit provider conflict')
   else:global_providers[n]=identity
   bind(p['source'],p['source_sha256']);bind(p['object'],p['object_sha256'])
  seen=set();toolnames={'Init'}
  def visit(n):
   if n=='Init'or n.startswith(('Lean.','Std.')):toolnames.add(n);return
   if n in seen:return
   need(n in providers,'Missing DFS provider');seen.add(n)
   for sub in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(providers[n]['source']).read_text(),re.M):visit(sub)
  for n in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M):visit(n)
  need(seen==set(providers)and toolnames==set(d['actual_direct_tool_imports']),'Prepared actual import DFS')
  roots=[Path(x)for x in d['LEAN_PATH'].split(':')if x];toolroot=Path(d['compiler']['path']).parent.parent/'lib/lean'
  def first(n):
   rel=Path(*n.split('.')).with_suffix('.olean')
   for root in roots+[toolroot]:
    q=root/rel
    if q.exists():return q
   raise ValueError('No first provider '+n)
  firsts={p['module']:p for p in d['actual_first_providers']};need(set(firsts)==set(providers),'All actual first project providers')
  for n,p in firsts.items():need(first(n)==Path(p['actual_first'])and first(n).resolve()==Path(p['resolved']).resolve()==Path(providers[n]['object']).resolve(),'Current actual first provider');bind(p['actual_first'],p['sha256'])
  tools={p['module']:p for p in d['toolchain_providers']};need(set(tools)==toolnames,'Explicit tools')
  for n,p in tools.items():bind(p['object'],p['object_sha256']);need(first(n).resolve()==Path(p['actual_first']).resolve()==Path(p['object']).resolve(),'Tool first provider')
  results.append({'module':module,'verification':{'path':str(vp),'sha256':sha(vp)},'source':{'path':str(source),'sha256':sha(source)},'audit':{'path':str(audit),'sha256':sha(audit)},'staged_guard_sha256':sha(staged),'project_providers':len(providers),'proof_commands':0,'fresh_modules':0,'installed_generated_parent_count':len(deps)})
 need(len(list((W/'prepared').rglob('verification.json')))==102,'Exactly102 actual preparation records')
 for p,target in targets.items():need(str(Path(p).resolve())==target,'Final input resolution changed')
 for p,h in resolved.items():need(sha(p)==h,'Final physical hash changed')
 O.mkdir();summary={'status':'INDEPENDENT_MAINTAINED_DEFAULT_PREPARATION_REVIEW_PASS','scope':'All102 installed-default preparation records only. No proof replay or fresh source object is claimed.','coordination':{'path':str(cpath),'sha256':ch,'status':c['status']},'manifest_sha256':MANIFEST_SHA,'coordinator_sha256':COORD_SHA,'python_guard_preparation_commands':102,'leaf_proof_commands':proof_commands,'leaf_fresh_modules':fresh,'leaf_status':'PREPARED_NOT_BUILT','all_source_audit_overrides_false':True,'all_version_query_build_download_flags_false':True,'all_source_audit_paths_are_installed_defaults':True,'site_parent':{'path':str(site),'sha256':m['site_parent']['sha256']},'generated_parent_record_bindings':direct_parent_count,'generated_parent_record_paths_are_installed':True,'exact_defaults_only_guard_diffs':102,'all_before_after_current_hashes_and_actual_providers_verified':True,'all_installed_manifest_artifacts_rehashed':True,'binding_checks':checks,'distinct_input_paths':len(paths),'distinct_resolved_files':len(resolved),'project_modules_across_all_preparations':len(global_providers),'final_unit_project_providers':results[-1]['project_providers'],'leaf_records':results,'findings':[],'historical_parent_note':'Installed Site and generated direct-parent verification paths are used. Raw parent records retain their original source/object/cache paths; those exact historical prerequisites remain explicit and were rehashed, not rebuilt.','reviewer_source':{'path':str(Path(__file__).resolve()),'sha256':sha(Path(__file__))},'compiler_invoked':False,'guard_or_coordinator_invoked':False,'supplied_checker_invoked':False,'version_queried':False,'dependency_build':False,'maintained_files_changed':False}
 (O/'review.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'input-bindings.json').write_text(json.dumps({'paths':paths,'resolved_targets':targets},indent=2)+'\n');print(json.dumps({'review':str(O/'review.json'),'sha256':sha(O/'review.json'),'input_bindings':str(O/'input-bindings.json'),'bindings_sha256':sha(O/'input-bindings.json'),'checks':checks,'leaves':len(results)},indent=2))
if __name__=='__main__':main()
