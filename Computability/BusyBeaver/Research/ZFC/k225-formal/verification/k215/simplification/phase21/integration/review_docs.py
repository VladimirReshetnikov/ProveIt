#!/usr/bin/env python3
"""Owned read-only final documentation, metric and publication-copy audit."""
import hashlib,json,re,subprocess
from pathlib import Path
from urllib.parse import unquote,urlsplit
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');B=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase21';L=B/'lean';I=B/'integration';OUT=Path('/tmp/k215-phase21-publication-peer/readback-v1.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pin(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
assert not OUT.exists()
adopt=read(I/'docs-adoption.json');assert len(adopt['docs'])==9
for r in adopt['docs']:assert sha(r['path'])==r['sha256']
a=read(L/'result-review.json');p=read(I/'progress.json');m=read(I/'metrics.json');c=read(I/'capture-review.json');s=read(I/'source-review.json');q=read(L/'check-plan.json');cap=read(L/'capture.json');cfg=read(L/'capture-config.json');spec=read(I/'source-spec.json')
assert a['status']=='PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK' and s['status']=='PASS_FINAL_SOURCE_REPAIR_AND_RELOCATION_PEER' and c['status']=='PASS_INDEPENDENT_ARCHIVE_INDEX_AND_REQUIRED_COVERAGE_REVIEW'
assert a['providers']==p['providers']==226 and a['projects']==211 and a['typed_clients']==15 and a['fresh']==p['fresh']==18 and a['reuses']==p['reused']==208 and a['audits']==p['audits']==2
assert [a[k] for k in ['client_reports','WFTheory_reports','audit_reports']]==[93,5,10]
assert a['fresh_provider_warnings']==p['fresh_warnings']==0 and a['reused_provider_warnings']==p['reused_warnings']==15
assert (a['raw_records_present'],a['raw_records_absent_inherited'],a['present_inputs_checked'],a['absences_checked'])==(195,31,55,16)
bindings=[(L/'result.json',a['result']['sha256']),(L/'check-plan.json',a['plan']['sha256']),(L/'check.py',a['runner']['sha256']),(L/'review_actual.py',a['auditor']['sha256']),(L/'evidence.tar.gz',c['archive']['sha256']),(L/'index.json',c['index']['sha256']),(L/'capture.json',c['capture_receipt']['sha256']),(L/'capture-config.json',c['config']['sha256']),(L/'capture.py',cap['capture_helper_sha256']),(I/'review_capture.py',c['auditor']['sha256']),(I/'review_sources.py',s['reader']['sha256'])]
for f,h in bindings:assert sha(f)==h
for key,f in [('result_sha256',L/'result.json'),('actual_review_sha256',L/'result-review.json'),('source_review_sha256',I/'source-review.json'),('capture_review_sha256',I/'capture-review.json'),('archive_sha256',L/'evidence.tar.gz')]:assert p[key]==sha(f)
assert (c['blob_members'],c['logical_entries'],c['source_aliases'],c['raw_files'],c['external_boundary_files'])==(585,3053,3038,2861,11)
assert cap['archive_bytes']==(L/'evidence.tar.gz').stat().st_size==5145190 and cap['objects_copied']==False and c['filesystem_archive_extraction']==False
assert len(cfg['external_boundaries'])==11
external=[]
for r in cfg['external_boundaries']:
 f=Path(r['source']);assert sha(f)==r['sha256'];rel=str(f.relative_to(ROOT));old=subprocess.run(['git','show','a113bb79e275c769c057fea7f6cc1540b0bfef32:'+rel],capture_output=True,check=True).stdout
 assert hashlib.sha256(old).hexdigest()==r['sha256'];external.append(pin(f))
retired=[]
for r in spec['retired_modules']+spec['retired_producers']:
 rel=('rotation240_pa/' if '/rotation240_pa/' in r['canonical'] else '')+Path(r['canonical']).name;f=B/'retired'/rel
 assert sha(f)==r['sha256']==sha(r['snapshot']) and not Path(r['canonical']).exists() and not Path(r['canonical']).is_symlink();retired.append(pin(f))
assert len(retired)==5
before_lines=after_lines=before_bytes=after_bytes=0
for r in m['source_rows']:
 for phase in ['before','after']:
  v=r[phase]
  if v:
   f=Path(v['path']);assert sha(f)==v['sha256'] and f.stat().st_size==v['bytes'] and len(f.read_bytes().splitlines())==v['lines']
 before_lines+=r['before']['lines'];before_bytes+=r['before']['bytes'];after_lines+=r['after']['lines'] if r['after'] else 0;after_bytes+=r['after']['bytes'] if r['after'] else 0
assert (before_lines,after_lines,before_lines-after_lines,before_bytes-after_bytes)==(1755,670,1085,104946)
assert m['Lean_savings']=={'lines':1085,'bytes':104946} and m['writer_savings']=={'lines':568,'bytes':21499} and m['total_active_savings']=={'lines':1653,'bytes':126445}
for r in m['retired_writer_rows']:assert sha(r['path'])==r['sha256'] and Path(r['path']).stat().st_size==r['bytes'] and len(Path(r['path']).read_bytes().splitlines())==r['lines']
assert sum(r['lines'] for r in m['retired_writer_rows'])==568 and sum(r['bytes'] for r in m['retired_writer_rows'])==21499
assert m['endpoint_closure']==q['endpoint_closure']=={'old_module_count':179,'old_source_bytes':1768653,'new_module_count':179,'new_source_bytes':1771267,'added_modules':[],'removed_modules':[]}
assert p['endpoint_source_delta_bytes']==2614 and p['goal_active'] and p['internal_PA_endpoint_still_open'] and p['minimum_state_theorem_still_open'] and p['primary_machine_unchanged']
assert m['status']=='KERNEL_AND_INDEPENDENT_ACTUAL_PASS_CAPTURE_PENDING' and 'Metrics snapshot predates capture' in p['scope']
fail=read(I/'failure-history.json');assert len(fail['contexts'])==11 and fail['provider_timeouts']==[6] and c['preserved_failed_contexts']==11
links=[];docs=[Path(r['path']) for r in adopt['docs']]+[L/'README.md']
for f in docs:
 rel=str(f.relative_to(ROOT));old=subprocess.run(['git','show','HEAD:'+rel],capture_output=True)
 if old.returncode==0:
  d=subprocess.run(['git','diff','HEAD','--',rel],capture_output=True,text=True,check=True).stdout;added='\n'.join(x[1:] for x in d.splitlines() if x.startswith('+') and not x.startswith('+++'))
 else:assert old.returncode==128;added=f.read_text()
 for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',added):
  u=urlsplit(target)
  if u.scheme or u.netloc:continue
  dest=(f.parent/unquote(u.path)).resolve();assert dest.exists(),(f,target)
  links.append({'document':str(f),'target':target,'resolved':str(dest)})
assert len(links)==39
machine={f:h for f,h in q['present_inputs'].items() if '/candidate-k215/' in f};assert len(machine)==3
for f,h in machine.items():assert sha(f)==h
leaf=(L/'README.md').read_text();top=(B/'README.md').read_text()
for token in ['215 states','internal PA endpoint','minimum-state theorem','Thirty-one inherited','Eleven failed prefixes','1,085 Lean lines','1,653 fewer','1,771,267','b87972c3f3de3116e0da6c42e2ada8a29bc2697e238cb635916fdfe9efc73e54']:assert token in leaf
for token in ['247 expression constructors','180 semantic macro effects','1.42 seconds','479 generated declarations','1,755 to 670 lines','+2,614 bytes','unchanged','internal PA endpoint']:assert token in top
for f in [*docs,*[I/x for x in ['progress.json','metrics.json','source-review.json','capture-review.json','failure-history.json','docs-adoption.json']]]:assert f.is_file()
report={'status':'PASS_INDEPENDENT_CANONICAL_DOCUMENT_LINK_METRIC_AND_RETIRED_BYTES_REVIEW','reader':pin(__file__),'adoption_record':pin(I/'docs-adoption.json'),'canonical_documents':[pin(f) for f in docs],'checked_new_local_links':len(links),'links':links,'accepted_result':pin(L/'result.json'),'actual_review':pin(L/'result-review.json'),'source_review':pin(I/'source-review.json'),'capture_review':pin(I/'capture-review.json'),'progress':pin(I/'progress.json'),'metrics':pin(I/'metrics.json'),'all_five_retired_snapshots':retired,'all_eleven_phase20_leaf_files_exact_at_a113':external,'three_machine_pins_unchanged':machine,'findings':[],'metrics_pending_status_is_explicitly_historical_snapshot':True,'claims_reviewed':['226 providers; 211 projects; 15 clients; 18 fresh; 208 reuses; 2 audits','93/5/10 exact report profiles; fresh zero warnings; 15 reused warning occurrences','195 adjacent raw records; accepted aggregate boundary for 31 absent inherited records','11 rejected contexts; only v6 is a wall timeout','247 expression constructors; 180 semantic macros before the terminal gate','Exact four public headers and ax_eval relocation; source/API review binding','1085 Lean and 568 writer lines saved; 126445 total source bytes saved','179-module primary endpoint grows by 2614 bytes; native scaffold savings have broader scope','215-state machine unchanged; internal PA endpoint and minimum-state theorem remain open'],'compiler_or_supplied_code_execution':False,'canonical_edits':False,'scope':'Current phase21 Lean leaf, all nine adopted documentation changes, current progress/metric/source/capture relations, five retired files, three machine pins and exact eleven-file historical phase20 leaf. Existing unrelated documentation and other variants full compiler stacks are outside this readback.'}
with OUT.open('x') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps({'status':report['status'],'report':pin(OUT)},indent=2))
