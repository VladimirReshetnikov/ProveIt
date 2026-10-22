#!/usr/bin/env python3
"""Own inert final runtime/config-input review; does not execute either helper."""
import hashlib,json
from pathlib import Path,PurePosixPath
P=Path('/tmp/k215-phase19-publication-draft');O=Path('/tmp/k215-phase19-capture-peer')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pin(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(O/'source-review.json')=='5dd1842bb3f675941df98ae45264a62e3e0e9551ef9bdfd0e70c8086e403c36c'
assert sha(P/'runtime-bindings-final.json')=='dd511fdfd4d23c4a12f4e90b55bce9feef17e3c649dd9f89059ff2e3e4c1ef2d'
assert sha(P/'capture-final.py')=='480a76e3fe9598fb3d5f3d75b1a52771cb27a100d6b4bdcf1ad4025f696711cd'
assert sha(P/'build_config-final.py')=='583b59da71860cb142c6662a812a1cd5c276bd9427886133c34b3a2a39976d17'
bindings=read(P/'runtime-bindings-final.json');cfg=read(P/'capture-config.template.json');actual=read(bindings['actual_review']);base=read(bindings['baseline_review'])
assert sha(bindings['actual_review'])=='829374ee6bfc13f52026c9f0d93c25c1719508f856273e35f1e7f8c3f93dde27'
assert sha(bindings['baseline_review'])=='543b35ffba8edb1be648747eb7f27aa5416345ee9e2e872b0e74385c8af46a57'
assert actual['status']=='PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK' and base['status']=='PASS_INDEPENDENT_ACTUAL_BASELINE_READBACK'
assert sha(bindings['actual_review_helper'])==actual['auditor']['sha256']=='9559d40c2f4b98cc82c6740ab932ae5ea421c50ebcd24ecf830bd6f7c6bd8341'
assert sha(bindings['baseline_review_helper'])==base['review_helper_sha256']=='c77fcf332bd4dd2f3ad557844832a93dc7787993ba78d35fb0d516fa76cf8c10'
assert (base['provider_count'],base['fresh_count'],base['reused_count'],base['audit_count'])==(226,12,214,0)
assert sum(base['fresh_warning_counts'].values())==base['fresh_warning_counts']['BusyBeaver.ZFC.L2Control219']==2
assert base['preserved_initial_failure']['failed_prefix_not_adopted']
raw={};input_pins=[]
def add(source,dest,h=None):
 p=Path(source);q=PurePosixPath(dest);assert p.is_absolute() and p.is_file() and not p.is_symlink() and 'objects' not in p.parts
 assert p.suffix not in {'.olean','.ilean','.o','.a','.so','.obj','.exe','.dll','.dylib'}
 assert not q.is_absolute() and '..' not in q.parts and str(q)==dest and dest not in raw
 digest=sha(p);assert h is None or digest==h
 raw[dest]={'source':str(p),'sha256':digest,'bytes':p.stat().st_size}
for name,counts in [('baseline',(12,214,0)),('candidate',(16,210,2))]:
 run=bindings['runs'][name];result=read(run['result']);plan=read(run['plan']);done=read(run['completed'])
 assert result['status']=='PASS' and result['provider_count']==226 and (len(result['fresh_modules']),len(result['reused_modules']),len(result['audits']))==counts
 assert result['map_sha256']==sha(run['plan']) and result['runner_sha256']==sha(run['runner'])
 for k,v in run.items():
  if k!='workspace':add(v,name+'/metadata/'+k+Path(v).suffix)
 add(Path(run['result']).parent/'toolchain.json',name+'/metadata/toolchain.json')
 for row in plan['modules']:add(Path(run['workspace'])/(row['module'].replace('.','/')+'.lean'),name+'/workspace/'+row['module'].replace('.','/')+'.lean',row['source_sha256'])
 for m in result['fresh_modules']:
  rec=done[m];d=Path(rec['log']).parent;label=name+'/attempts/'+d.name
  assert read(d/'record.json')==rec
  add(d/(m.split('.')[-1]+'.lean'),label+'/source.lean',rec['source_sha256']);add(rec['log'],label+'/compiler.log',rec['log_sha256']);add(d/'record.json',label+'/record.json')
 for rec in result['audits']:
  d=Path(rec['log']).parent;label=name+'/audits/'+rec['module'];assert read(d/'record.json')==rec
  add(rec['source'],label+'/source.lean',rec['source_sha256']);add(rec['log'],label+'/compiler.log',rec['log_sha256']);add(d/'record.json',label+'/record.json')
assert len(raw)==562 and sum('/workspace/' in n for n in raw)==452
assert sum('/attempts/' in n for n in raw)==84 and sum('/audits/' in n for n in raw)==6
files=list(cfg['files']);known={(r['source'],r['sha256']) for r in files};assert len(bindings['extra_files'])==31
for row in bindings['extra_files']:
 p=Path(row['source']);assert p.is_file() and not p.is_symlink();h=sha(p);files.append({**row,'sha256':h});known.add((str(p),h));input_pins.append(pin(p))
external={r['source']:r['sha256'] for r in cfg['external_boundaries']};candidate=read(bindings['runs']['candidate']['plan']);auto=0
for source,h in candidate['present_inputs'].items():
 assert sha(source)==h
 if source in external:assert external[source]==h
 elif (source,h) not in known:files.append({'source':source,'sha256':h,'logical':'frozen-inputs/'+source.lstrip('/'),'role':'candidate_frozen_present_input'});known.add((source,h));auto+=1
assert auto==9
for source,name in [(P/'build_config-final.py','context/publication/build_config.py'),(P/'runtime-bindings-final.json','context/publication/runtime-bindings.json'),(P/'capture-config.template.json','context/publication/config-template.json')]:files.append({'source':str(source),'sha256':sha(source),'logical':name,'role':'owned_capture_configuration_provenance'})
assert len(files)==len({r['logical'] for r in files})==123
all_logical=['runtime/'+n for n in raw]+[r['logical'] for r in files]+[r['logical'] for r in cfg['external_boundaries']]+['capture/'+n for n in ['actual-review.json','review_actual.py','baseline-review.json','review_baseline.py','raw-copy-plan.json','capture.py','config.json']]
assert len(all_logical)==len(set(all_logical))==703
report={'status':'PASS_FINAL_CAPTURE_HELPER_BUILDER_AND_RUNTIME_BINDINGS_SOURCE_REVIEW','initial_source_review':pin(O/'source-review.json'),'inputs':[pin(P/n) for n in ['capture-final.py','build_config-final.py','capture-config.template.json','runtime-bindings-final.json','final-source-handoff.json']],'baseline_review':pin(bindings['baseline_review']),'candidate_review':pin(bindings['actual_review']),'runtime_extra_pins':input_pins,'expected_raw_files':562,'expected_workspace_sources':452,'expected_accepted_fresh_attempt_triples':28,'expected_audit_triples':2,'expected_metadata_files':20,'expected_context_rows':123,'expected_logical_entries':703,'external_boundary_files':11,'automatic_current_frozen_input_rows':9,'historical_producer_before_snapshot_checked':True,'failed_old_baseline_ten_attempts_and_metadata_preserved':True,'all_candidate_present_pins_current_and_bound':True,'logical_names_unique':True,'findings':[],'recommendation':'Root may execute the reviewed config builder in a new output directory, inspect its exact config/raw counts and pins, then execute the reviewed capture once in a separate new directory. Independent actual archive verification follows; source review is not capture acceptance.','no_builder_capture_generator_Lean_or_archived_code_execution':True,'no_canonical_or_staging_writes':True}
(O/'final-source-review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'review':pin(O/'final-source-review.json')},indent=2))
