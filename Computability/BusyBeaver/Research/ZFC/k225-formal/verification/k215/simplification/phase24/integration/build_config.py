#!/usr/bin/env python3
"""Owned inert config/raw-plan builder; root reviews before execution.

Reads one terminal accepted run, an independent actual readback and explicit failed
run roots. Writes only new JSON manifests. Never invokes a compiler, producer or capture.
"""
from pathlib import Path
import argparse,hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PREVIOUS=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase23/lean'
CORE=['README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py']
BASIS_SHA='684d93cbb3b49a25587ca2177d49789ff8e6dad0c06e5f9823803d665304cffe'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pinned(p,expected=None):
 p=Path(p).absolute();assert p.is_file()and not p.is_symlink()and'objects'not in p.parts
 h=sha(p)
 if expected is not None:assert h==expected,p
 return {'source':str(p),'sha256':h}
def freeze_for(root,outer):
 matches=[p for p in root.glob('freeze*.json')if sha(p)==outer['freeze_sha256']]
 assert len(matches)==1,(root,matches);return matches[0]
def run_receipts(root,accepted):
 root=Path(root).absolute();outer_path=root/'candidate-build-outer.json';outer=read(outer_path)
 assert outer['exit_code']==0 if accepted else outer['exit_code']!=0
 assert outer['status']=='PASS_EXIT_ZERO'if accepted else outer['status']!='PASS_EXIT_ZERO'
 argv=outer['argv'];assert argv[:2]==['python3','-B']and argv[3]=='--map'and argv[5]=='--out'
 directory=Path(argv[6]);assert directory==root/'candidate-build-run1'
 paths={'plan':Path(argv[4]),'runner':Path(argv[2]),'outer':outer_path,'stdout':root/'candidate-build.stdout','stderr':root/'candidate-build.stderr','freeze':freeze_for(root,outer),'launcher':root/'run_once.py'}
 for n,h in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('freeze','freeze_sha256'),('launcher','launcher_sha256')]:assert sha(paths[n])==outer[h]
 assert sha(paths['runner'])==args.runner_sha
 return directory,paths,outer
parser=argparse.ArgumentParser();parser.add_argument('--run-root',type=Path,required=True);parser.add_argument('--runner-sha',required=True);parser.add_argument('--failed-root',type=Path,action='append',default=[]);parser.add_argument('--review',type=Path,required=True);parser.add_argument('--review-sha',required=True);parser.add_argument('--review-helper',type=Path,required=True);parser.add_argument('--review-helper-sha',required=True);parser.add_argument('--capture-helper',type=Path,required=True);parser.add_argument('--extra-file',nargs=3,action='append',default=[],metavar=('PATH','SHA256','ROLE'));parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
review_row=pinned(args.review,args.review_sha);review=read(args.review);review_helper=pinned(args.review_helper,args.review_helper_sha)
assert review['status']=='PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK'
assert review['exact_profiles_preserved']and review['all_source_object_dependency_log_toolchain_bindings_checked']
assert review['fresh_provider_warnings']==review['fresh_client_audit_warnings']==0
assert (review['client_reports'],review['WFTheory_reports'],review['audit_reports'])==(93,5,10)
assert review['auditor']['path']==review_helper['source']and review['auditor']['sha256']==review_helper['sha256']
run_dir,paths,outer=run_receipts(args.run_root,True)
for n in['result','inventory','completed','before','toolchain']:paths[n]=run_dir/(n+'.json')
result=read(paths['result']);plan=read(paths['plan']);done=read(paths['completed'])
expected={'providers':plan['expected']['provider_count'],'projects':plan['expected']['project_count'],'typed_clients':plan['expected']['typed_client_count'],'fresh':len(plan['expected']['fresh_by_source_transitivity']),'reuses':plan['expected']['provider_count']-len(plan['expected']['fresh_by_source_transitivity']),'audits':len(plan['audits']),'absences':len(plan['absent_inputs'])}
assert result['status']=='PASS'and result['provider_count']==len(plan['modules'])==len(done)==expected['providers']
assert all(review[k]==expected[k]for k in ['providers','projects','typed_clients','fresh','reuses','audits'])
assert(len(result['fresh_modules']),len(result['reused_modules']),len(result['audits']))==(expected['fresh'],expected['reuses'],expected['audits'])
assert set(result['fresh_modules'])==set(plan['expected']['fresh_by_source_transitivity'])
assert result['basis_result_sha256']==BASIS_SHA==sha(PREVIOUS/'result.json')
assert result['map_sha256']==sha(paths['plan'])and result['runner_sha256']==sha(paths['runner'])
assert result['completed_sha256']==sha(paths['completed'])and result['inventory_sha256']==sha(paths['inventory'])
assert review['result']['path']==str(paths['result'])and review['result']['sha256']==sha(paths['result'])
raw=[];destinations=set();context_rows=[]
def raw_add(p,destination,role,historical=None):
 row=pinned(p);assert destination not in destinations;destinations.add(destination)
 row.update(destination=destination,bytes=Path(p).stat().st_size,role=role)
 if historical is not None:row['historical_source']=historical
 raw.append(row);return {'source':row['source'],'sha256':row['sha256']}
def add_run_files(directory,paths,prefix,accepted):
 rows=[]
 for n,p in sorted(paths.items()):rows.append(raw_add(p,prefix+'/receipts/'+n+p.suffix,'accepted_candidate_receipt'if accepted else'preserved_unaccepted_run_receipt'))
 for n in['before','inventory','completed','toolchain']:
  p=directory/(n+'.json')
  if p.is_file()and p not in paths.values():rows.append(raw_add(p,prefix+'/receipts/'+p.name,'accepted_candidate_receipt'if accepted else'preserved_unaccepted_run_receipt'))
 module_rows={r['module']:r for r in read(paths['plan'])['modules']}
 workspace=directory/'workspace'
 for p in sorted(workspace.rglob('*.lean')):
  module='.'.join(p.relative_to(workspace).with_suffix('').parts);r=module_rows[module]
  assert sha(p)==r['source_sha256']
  rows.append(raw_add(p,prefix+'/workspace/'+p.relative_to(workspace).as_posix(),'accepted_workspace_source'if accepted else'preserved_unaccepted_workspace_source',r['source']))
 for p in sorted((directory/'attempts').rglob('*'))if(directory/'attempts').is_dir()else[]:
  if p.is_file():
   assert p.name in['compiler.log','record.json','assumption-profile-discrepancy.json']or p.suffix=='.lean',p
   rows.append(raw_add(p,prefix+'/attempts/'+p.relative_to(directory/'attempts').as_posix(),'accepted_current_attempt_evidence'if accepted else'preserved_unaccepted_attempt_evidence'))
 for d in sorted(directory.glob('audit-*')):
  for p in sorted(d.iterdir()):
   if p.is_file()and p.suffix!='.olean':
    assert p.name in['compiler.log','record.json','assumption-profile-discrepancy.json']or p.suffix=='.lean',p
    rows.append(raw_add(p,prefix+'/'+d.name+'/'+p.name,'accepted_endpoint_audit_evidence'if accepted else'preserved_unaccepted_audit_evidence'))
 return rows
add_run_files(run_dir,paths,'candidate',True)
for i,root in enumerate(args.failed_root,1):
 directory,failed_paths,failed_outer=run_receipts(root,False)
 assert not(directory/'result.json').exists(),'A preserved failed prefix must not masquerade as a terminal accepted run.'
 name='failed-'+str(i);rows=add_run_files(directory,failed_paths,name,False)
 context_rows.append({'name':name,'terminal_status':failed_outer['status'],'accepted_as_current_result':False,'outer':pinned(failed_paths['outer']),'files':rows})
# Every accepted raw source/log/record must be covered, independently of glob discovery.
covered={r['source']:r['sha256']for r in raw}
for m in result['fresh_modules']:
 r=done[m];assert r['status']=='PASS'and r['exit_code']==0 and not r['timed_out']and r['warnings']==0
 assert covered.get(r['log'])==r['log_sha256']
 for p in[Path(r['log']).with_name('record.json'),Path(r['log']).with_name(m.split('.')[-1]+'.lean')]:assert str(p)in covered
for r in result['audits']:
 assert r['status']=='PASS'and r['exit_code']==0 and r['warnings']==0
 assert covered.get(r['source'])==r['source_sha256']and covered.get(r['log'])==r['log_sha256']
files=[];file_sources=set()
def file_add(p,h,role):
 p=Path(p).absolute()
 if p.is_relative_to(PREVIOUS):assert p.name in CORE;return
 if str(p)in file_sources:return
 file_sources.add(str(p));row=pinned(p,h);row.update(logical='inputs/'+str(len(files)+1).zfill(3)+'-'+p.name,role=role);files.append(row)
for p,h in sorted(plan['present_inputs'].items()):file_add(p,h,'current_plan_present_input')
for p,h,role in args.extra_file:file_add(p,h,role)
file_add(Path(__file__).resolve(),sha(__file__),'owned_config_builder')
for p in plan['absent_inputs']:assert not Path(p).exists()and not Path(p).is_symlink()
boundary=[{**pinned(PREVIOUS/n),'logical':'external/phase23/lean/'+n}for n in CORE]
out=args.out.absolute();assert not out.exists()and not out.is_symlink();out.mkdir(parents=True)
def save(p,data):
 with p.open('x')as f:json.dump(data,f,indent=2);f.write('\n')
raw_path=out/'raw-copy-plan.json';save(raw_path,{'status':'DRAFT_COPY_PLAN_NO_MUTATION','files':raw,'current_accepted_runs':1,'preserved_failed_context_count':len(context_rows),'scope':'Explicit current terminal accepted source/raw receipts plus separate unaccepted failed prefixes. No objects or previous packet archive copied.'})
cfg={'expected_counts':expected,'status':'FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS','capture_helper_sha256':sha(args.capture_helper),'actual_review':review_row,'actual_review_helper':review_helper,'external_boundaries':boundary,'files':files,'raw_copy_plan':pinned(raw_path),'runs':{'candidate':{'workspace':str(run_dir/'workspace'),**{n:pinned(p)for n,p in paths.items()}}},'failed_contexts':context_rows,'scope':'One accepted phase24 run. Phase23 stays an exact eleven-file external boundary; failed prefixes remain explicitly unaccepted source/raw context. No supplied code or proof execution.'}
config_path=out/'capture-config.json';save(config_path,cfg)
print(json.dumps({'status':'CONFIG_AND_RAW_PLAN_WRITTEN_NO_CAPTURE_EXECUTION','config':str(config_path),'config_sha256':sha(config_path),'raw_copy_plan_sha256':sha(raw_path),'raw_files':len(raw),'static_files':len(files),'failed_contexts':len(context_rows),'current_runs':1,'capture_helper_sha256':cfg['capture_helper_sha256']},indent=2))
