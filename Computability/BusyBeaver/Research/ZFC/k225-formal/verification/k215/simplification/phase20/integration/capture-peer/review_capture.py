#!/usr/bin/env python3
"""Independent read-only phase20 packet inspection; no extraction or captured code execution."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,re,tarfile
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PREVIOUS=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase19/lean'
CORE={'README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py'}
FORBIDDEN={'.olean','.ilean','.o','.obj','.a','.so','.dylib','.dll','.exe'}
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def pin(p):return dict(path=str(p),sha256=digest(p),bytes=Path(p).stat().st_size)
def safe(name):
 p=PurePosixPath(name);assert name and not p.is_absolute() and '..' not in p.parts and str(p)==name and '\\' not in name and '\x00' not in name
 assert p.suffix not in FORBIDDEN and 'objects' not in p.parts
 return name

def main():
 parser=argparse.ArgumentParser()
 for key in ['packet','config','output']:parser.add_argument('--'+key,type=Path,required=True)
 parser.add_argument('--config-sha',required=True);parser.add_argument('--capture-helper-sha',required=True);a=parser.parse_args()
 assert not a.output.exists() and digest(a.config)==a.config_sha
 cfg=read(a.config);index=read(a.packet/'index.json');capture=read(a.packet/'capture.json');archive=a.packet/'evidence.tar.gz'
 assert cfg['status']=='FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS' and capture['status']=='PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION'
 assert capture['config_sha256']==a.config_sha and cfg['capture_helper_sha256']==capture['capture_helper_sha256']==a.capture_helper_sha
 assert digest(archive)==index['archive_sha256']==capture['archive_sha256'] and digest(a.packet/'index.json')==capture['index_sha256']
 assert archive.stat().st_size==capture['archive_bytes'] and not capture['compiler_execution'] and not capture['supplied_code_execution'] and not capture['objects_copied']
 assert capture['current_runs']==1 and capture['preserved_failed_contexts']==3 and set(cfg['runs'])=={'candidate'}
 raw=read(cfg['raw_copy_plan']['source']);assert digest(cfg['raw_copy_plan']['source'])==cfg['raw_copy_plan']['sha256'] and raw['status']=='DRAFT_COPY_PLAN_NO_MUTATION'
 expected_raw={};historical={};logical={};sources={};blobs={};pins={}
 def require(source,dest,role,h=None,hist=None):
  source=Path(source);safe(dest);assert dest not in expected_raw
  row=dict(source=str(source),sha256=h or digest(source),destination=dest,bytes=source.stat().st_size,role=role)
  if hist is not None:row['historical_source']=hist
  expected_raw[dest]=row
 def run_files(directory,paths,prefix,accepted):
  for key,row in paths.items():
   if key!='workspace':require(row['source'],prefix+'/receipts/'+key+Path(row['source']).suffix,'accepted_candidate_receipt' if accepted else 'preserved_unaccepted_run_receipt',row['sha256'])
  known={row['source'] for key,row in paths.items() if key!='workspace'}
  for key in ['before','inventory','completed','toolchain']:
   source=directory/(key+'.json')
   if source.is_file() and str(source) not in known:require(source,prefix+'/receipts/'+source.name,'accepted_candidate_receipt' if accepted else 'preserved_unaccepted_run_receipt')
  plan=read(paths['plan']['source']);rows={row['module']:row for row in plan['modules']};workspace=directory/'workspace'
  for source in sorted(workspace.rglob('*.lean')):
   rel=source.relative_to(workspace);module='.'.join(rel.with_suffix('').parts);row=rows[module];assert digest(source)==row['source_sha256']
   require(source,prefix+'/workspace/'+rel.as_posix(),'accepted_workspace_source' if accepted else 'preserved_unaccepted_workspace_source',row['source_sha256'],row['source'])
   if accepted:historical[str(source)]=row['source']
  for source in sorted((directory/'attempts').rglob('*')):
   if source.is_file():
    assert source.name in ['compiler.log','record.json','assumption-profile-discrepancy.json'] or source.suffix=='.lean'
    require(source,prefix+'/attempts/'+source.relative_to(directory/'attempts').as_posix(),'accepted_current_attempt_evidence' if accepted else 'preserved_unaccepted_attempt_evidence')
  for audit in sorted(directory.glob('audit-*')):
   for source in sorted(audit.iterdir()):
    if source.is_file() and source.suffix!='.olean':
     assert source.name in ['compiler.log','record.json','assumption-profile-discrepancy.json'] or source.suffix=='.lean'
     require(source,prefix+'/'+audit.name+'/'+source.name,'accepted_endpoint_audit_evidence' if accepted else 'preserved_unaccepted_audit_evidence')
 run=cfg['runs']['candidate'];directory=Path(run['result']['source']).parent;run_files(directory,run,'candidate',True)
 plan=read(run['plan']['source']);res=read(run['result']['source']);done=read(run['completed']['source'])
 assert res['status']=='PASS' and res['provider_count']==len(plan['modules'])==len(done)==227
 assert (len(res['fresh_modules']),len(res['reused_modules']),len(res['audits']))==(14,213,2)
 assert digest(run['result']['source'])=='a334d6f473529c70bfc07dc16ad49bf2f7f0902a3ed39f6f30734e8886700e0d'
 assert {str(directory/'workspace'/(row['module'].replace('.','/')+'.lean')) for row in plan['modules']}==set(historical)
 failed_roots=[Path('/tmp/k215-phase20-check'),Path('/tmp/k215-phase20-check-v2'),Path('/tmp/k215-phase20-check-v3')]
 assert len(cfg['failed_contexts'])==3
 for i,(context,root) in enumerate(zip(cfg['failed_contexts'],failed_roots),1):
  assert context['name']=='failed-'+str(i) and not context['accepted_as_current_result'] and Path(context['outer']['source']).parent==root
  outer=read(context['outer']['source']);assert outer['status']=='FAIL' and outer['exit_code']==1
  failed=Path(outer['argv'][6]);assert failed==root/'candidate-build-run1' and not (failed/'result.json').exists()
  paths={key:dict(source=str(source),sha256=digest(source)) for key,source in {'plan':Path(outer['argv'][4]),'runner':Path(outer['argv'][2]),'outer':root/'candidate-build-outer.json','stdout':root/'candidate-build.stdout','stderr':root/'candidate-build.stderr','freeze':next(source for source in root.glob('*.json') if digest(source)==outer['freeze_sha256']),'launcher':root/'run_once.py'}.items()}
  run_files(failed,paths,context['name'],False)
 assert {row['destination']:row for row in raw['files']}==expected_raw
 def expect(row,name,role,external=False):
  safe(name);assert name not in logical;p=Path(row['source']);assert p.is_absolute() and '..' not in p.parts and p.is_file() and not p.is_symlink()
  assert p.suffix not in FORBIDDEN and 'objects' not in p.parts;b=p.read_bytes();h=hashlib.sha256(b).hexdigest();assert h==row['sha256'];pins[str(p)]=h
  item=dict(source=str(p),sha256=h,bytes=len(b),role=role)
  if 'historical_source' in row:item['historical_source']=row['historical_source']
  if external:item['external']=True
  else:
   assert not p.is_relative_to(PREVIOUS) and not str(p).endswith(('.tar','.tar.gz','.tgz','.zip'));item['blob']='blobs/'+h;blobs[h]=b
  logical[name]=item;alias=sources.setdefault(str(p),dict(sha256=h,bytes=len(b),external=external,logical=[]));assert (alias['sha256'],alias['bytes'],alias['external'])==(h,len(b),external);alias['logical'].append(name)
 for row in raw['files']:
  item=dict(row)
  if item['source'] in historical:item['historical_source']=historical[item['source']]
  expect(item,'runtime/'+safe(item['destination']),item.get('role','accepted_candidate_raw'))
 for row in cfg['files']:expect(row,row['logical'],row['role'])
 assert {row['source'] for row in cfg['external_boundaries']}=={str(PREVIOUS/name) for name in CORE}
 for row in cfg['external_boundaries']:expect(row,row['logical'],'exact_phase19_leaf_boundary',True)
 for key,name in [('actual_review','capture/actual-review.json'),('actual_review_helper','capture/review_actual.py'),('raw_copy_plan','capture/raw-copy-plan.json')]:expect(cfg[key],name,key)
 expect(dict(source=index['logical']['capture/capture.py']['source'],sha256=a.capture_helper_sha),'capture/capture.py','owned_capture_helper')
 expect(dict(source=str(a.config.absolute()),sha256=a.config_sha),'capture/config.json','owned_capture_config')
 for alias in sources.values():alias['logical'].sort()
 assert index['format']=='phase20-explicit-evidence-blobs-v1' and index['logical']==logical and index['sources']==sources
 assert index['external_boundaries']=={row['source']:row['sha256'] for row in cfg['external_boundaries']}
 assert (len(blobs),len(logical),len(sources),len(raw['files']))==(capture['blob_members'],capture['logical_entries'],capture['source_aliases'],capture['raw_plan_files'])
 assert capture['external_boundary_files']==11
 data=archive.read_bytes();assert data[:8]==bytes([31,139,8,0,0,0,0,0])
 with tarfile.open(archive,'r:gz') as tar:
  members=tar.getmembers();assert [member.name for member in members]==sorted('blobs/'+h for h in blobs)
  for member in members:
   assert re.fullmatch(r'blobs/[0-9a-f]{64}',member.name) and safe(member.name)==member.name and member.isfile() and not member.issym() and not member.islnk()
   assert (member.mode,member.uid,member.gid,member.mtime,member.uname,member.gname)==(0o644,0,0,0,'','')
   b=tar.extractfile(member).read();assert b==blobs[member.name[6:]] and hashlib.sha256(b).hexdigest()==member.name[6:] and len(b)==member.size
 for path,h in plan['present_inputs'].items():assert digest(path)==h and pins.get(path)==h
 for path in plan['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink()
 specpath=Path('/tmp/k215-phase20-repairs/source-spec-v4.json');assert pins.get(str(specpath))==digest(specpath);spec=read(specpath)
 for row in spec['sources']:assert pins[row['candidate']['path']]==row['candidate']['sha256']
 assert len(spec['retired_producers'])==3
 for row in spec['retired_producers']:assert pins[row['snapshot']]==row['sha256'] and not Path(row['canonical']).exists()
 for m in res['fresh_modules']:
  row=done[m];record=Path(row['log']).with_name('record.json');assert read(record)==row and row['status']=='PASS' and row['exit_code']==0 and not row['timed_out'] and row['warnings']==0
  assert pins[row['log']]==row['log_sha256'] and pins[str(record)]==digest(record) and pins[str(record.parent/(m.split('.')[-1]+'.lean'))]==row['source_sha256']
 for row in res['audits']:
  record=Path(row['log']).with_name('record.json');assert read(record)==row and row['status']=='PASS' and row['exit_code']==0 and row['warnings']==0
  assert pins[row['source']]==row['source_sha256'] and pins[row['log']]==row['log_sha256'] and str(record) in pins
 assert pins.get('/tmp/k215-phase20-runner-peer/repair-review-v1.json')=='185f3eaab70cc26f9ea7f09a635638ccf1f97d9efb85f381252e3ebe6f719b9a'
 for path,h in pins.items():assert digest(path)==h
 report=dict(status='PASS_INDEPENDENT_ARCHIVE_INDEX_AND_REQUIRED_COVERAGE_REVIEW',auditor=pin(__file__),archive=pin(archive),index=pin(a.packet/'index.json'),capture_receipt=pin(a.packet/'capture.json'),config=pin(a.config),blob_members=len(blobs),logical_entries=len(logical),source_aliases=len(sources),external_boundary_files=11,raw_files=len(raw['files']),checked_current_workspace_sources=227,accepted_fresh_attempt_triples=14,candidate_audit_triples=2,preserved_failed_contexts=3,all_member_hashes_bytes_and_metadata_exact=True,complete_logical_and_source_alias_index_reconstructed=True,final_source_spec_and_all_retired_snapshots_covered=True,all_current_candidate_present_pins_checked=len(plan['present_inputs']),all_required_absences_checked=len(plan['absent_inputs']),objects_copied=False,filesystem_archive_extraction=False,archived_code_Lean_generator_or_capture_helper_execution=False,scope='Independent in-memory member inspection and exact index/source-alias reconstruction, including all required current raw evidence and three explicitly rejected runtime histories. Phase19 remains an eleven-file external boundary.')
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status=report['status'],review=pin(a.output))))
if __name__=='__main__':main()
