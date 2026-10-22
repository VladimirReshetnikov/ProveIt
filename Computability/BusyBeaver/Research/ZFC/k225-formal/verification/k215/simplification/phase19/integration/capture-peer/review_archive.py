#!/usr/bin/env python3
"""Independent read-only archive/index audit; never executes or extracts captured code."""
import hashlib,json,re,tarfile
from collections import defaultdict
from pathlib import Path,PurePosixPath
O=Path('/tmp/k215-phase19-capture-peer');P=Path('/tmp/k215-phase19-publication-capture');C=Path('/tmp/k215-phase19-publication-config');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda b:hashlib.sha256(b).hexdigest()
def digest(p):return sha(Path(p).read_bytes())
def read(p):return json.loads(Path(p).read_text())
def pin(p):p=Path(p);return {'path':str(p),'sha256':digest(p),'bytes':p.stat().st_size}
def safe(n):
 p=PurePosixPath(n);assert n and not p.is_absolute() and '..' not in p.parts and str(p)==n and '\\' not in n and '\x00' not in n
 return n

def main():
 output=O/'actual-review.json';assert not output.exists()
 configpath=C/'capture-config.json';cfg=read(configpath);raw=read(cfg['raw_copy_plan']['source']);index=read(P/'index.json');receipt=read(P/'capture.json');archive=P/'evidence.tar.gz'
 assert digest(configpath)=='c1c929146c2590e38c624c9a65826a6e8124e392f372f7b1aebebdf7f9e3fd21'
 assert digest(archive)==index['archive_sha256']==receipt['archive_sha256']=='920ba7ee18c35a92beed8be57f089d04ff622620fd58eff535c08ca9eea9e612'
 assert digest(P/'index.json')==receipt['index_sha256']=='5348190a6f2e3e3d6472d9d13b5237d62cab4fb8b0b26446348ec51642b911dd'
 assert archive.stat().st_size==receipt['archive_bytes']==1314141
 assert receipt['status']=='PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION' and cfg['status']=='FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS'
 assert receipt['capture_helper_sha256']==cfg['capture_helper_sha256']=='480a76e3fe9598fb3d5f3d75b1a52771cb27a100d6b4bdcf1ad4025f696711cd'
 assert receipt['config_sha256']==digest(configpath) and digest(cfg['raw_copy_plan']['source'])==cfg['raw_copy_plan']['sha256']
 assert receipt['actual_review_sha256']==cfg['actual_review']['sha256']=='829374ee6bfc13f52026c9f0d93c25c1719508f856273e35f1e7f8c3f93dde27'
 assert receipt['baseline_review_sha256']==cfg['baseline_review']['sha256']=='543b35ffba8edb1be648747eb7f27aa5416345ee9e2e872b0e74385c8af46a57'
 assert not receipt['objects_copied'] and not receipt['compiler_execution'] and not receipt['supplied_code_execution']
 assert len(raw['files'])==receipt['raw_plan_files']==562 and len(cfg['files'])==133 and len(cfg['external_boundaries'])==11
 forbidden={'.olean','.ilean','.o','.obj','.a','.so','.dylib','.dll','.exe'}
 logical={};sources={};blobbytes={};pins={};historical={};expected_raw={}
 def expect(row,name,role,external=False):
  safe(name);assert name not in logical
  p=Path(row['source']);assert p.is_absolute() and '..' not in p.parts and p.is_file() and not p.is_symlink()
  assert p.suffix not in forbidden and 'objects' not in p.parts
  b=p.read_bytes();h=sha(b);assert h==row['sha256'];pins[str(p)]=h
  item={'source':str(p),'sha256':h,'bytes':len(b),'role':role}
  if 'historical_source' in row:item['historical_source']=row['historical_source']
  if external:item['external']=True
  else:
   assert not str(p).endswith(('.tar','.tar.gz','.tgz','.zip'))
   item['blob']='blobs/'+h;blobbytes[h]=b
  logical[name]=item
  prior=sources.setdefault(str(p),{'sha256':h,'bytes':len(b),'external':external,'logical':[]})
  assert (prior['sha256'],prior['bytes'],prior['external'])==(h,len(b),external)
  prior['logical'].append(name)
 # Derive exact raw coverage independently from accepted selections and records.
 for name,counts in [('baseline',(12,214,0)),('candidate',(16,210,2))]:
  run=cfg['runs'][name];plan=read(run['plan']['source']);res=read(run['result']['source']);done=read(run['completed']['source']);workspace=Path(run['workspace'])
  assert res['status']=='PASS' and res['provider_count']==226 and (len(res['fresh_modules']),len(res['reused_modules']),len(res['audits']))==counts
  def required(source,dest,h=None):
   assert dest not in expected_raw;expected_raw[dest]={'source':str(source),'sha256':h or digest(source),'bytes':Path(source).stat().st_size}
  for key,row in run.items():
   if key!='workspace':required(row['source'],name+'/metadata/'+key+Path(row['source']).suffix,row['sha256'])
  required(Path(run['result']['source']).parent/'toolchain.json',name+'/metadata/toolchain.json')
  for row in plan['modules']:
   rel=row['module'].replace('.','/')+'.lean';path=workspace/rel;required(path,name+'/workspace/'+rel,row['source_sha256']);historical[str(path)]=row['source']
  for m in res['fresh_modules']:
   rec=done[m];directory=Path(rec['log']).parent;label=name+'/attempts/'+directory.name
   assert read(directory/'record.json')==rec
   required(directory/(m.split('.')[-1]+'.lean'),label+'/source.lean',rec['source_sha256']);required(rec['log'],label+'/compiler.log',rec['log_sha256']);required(directory/'record.json',label+'/record.json')
  for rec in res['audits']:
   directory=Path(rec['log']).parent;label=name+'/audits/'+rec['module'];assert read(directory/'record.json')==rec
   required(rec['source'],label+'/source.lean',rec['source_sha256']);required(rec['log'],label+'/compiler.log',rec['log_sha256']);required(directory/'record.json',label+'/record.json')
 assert {r['destination']:{k:v for k,v in r.items() if k!='destination'} for r in raw['files']}==expected_raw and len(expected_raw)==562
 for row in raw['files']:
  item=dict(row)
  if item['source'] in historical:item['historical_source']=historical[item['source']]
  expect(item,'runtime/'+safe(item['destination']),'accepted_baseline_or_candidate_raw')
 for row in cfg['files']:expect(row,row['logical'],row['role'])
 previous=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase18/lean'
 core={'README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py'}
 assert {r['source'] for r in cfg['external_boundaries']}=={str(previous/n) for n in core}
 for row in cfg['external_boundaries']:expect(row,row['logical'],'exact_phase18_leaf_boundary',True)
 for key,name in [('actual_review','actual-review.json'),('actual_review_helper','review_actual.py'),('baseline_review','baseline-review.json'),('baseline_review_helper','review_baseline.py'),('raw_copy_plan','raw-copy-plan.json')]:expect(cfg[key],'capture/'+name,key)
 helper=index['logical']['capture/capture.py']['source'];expect({'source':helper,'sha256':cfg['capture_helper_sha256']},'capture/capture.py','owned_capture_helper')
 expect({'source':str(configpath),'sha256':digest(configpath)},'capture/config.json','owned_capture_config')
 for row in sources.values():row['logical'].sort()
 assert index['format']=='phase19-explicit-evidence-blobs-v1' and index['logical']==logical and index['sources']==sources
 external={r['source']:r['sha256'] for r in cfg['external_boundaries']};assert index['external_boundaries']==external
 assert len(logical)==receipt['logical_entries']==713 and len(sources)==receipt['source_aliases']==712 and len(blobbytes)==receipt['blob_members']==396
 assert receipt['external_boundary_files']==11
 # Inspect archive members strictly in memory; never extract to disk or execute member content.
 data=archive.read_bytes();assert data[:4]==bytes([31,139,8,0]) and data[4:8]==bytes(4)
 with tarfile.open(archive,'r:gz') as tar:
  members=tar.getmembers();assert len(members)==396 and [m.name for m in members]==sorted('blobs/'+h for h in blobbytes)
  assert len({m.name for m in members})==396
  for m in members:
   assert re.fullmatch(r'blobs/[0-9a-f]{64}',m.name) and safe(m.name)==m.name and m.isfile() and not m.issym() and not m.islnk()
   assert (m.mode,m.uid,m.gid,m.mtime,m.uname,m.gname)==(0o644,0,0,0,'','')
   b=tar.extractfile(m).read();assert b==blobbytes[m.name[6:]] and sha(b)==m.name[6:] and len(b)==m.size
 # Current pins must bind actual byte-provider paths; historical identities are labels only.
 candidate=read(cfg['runs']['candidate']['plan']['source']);baseline=read(cfg['runs']['baseline']['plan']['source'])
 for p,h in candidate['present_inputs'].items():assert digest(p)==h and pins.get(p)==h
 hist={(v['historical_source'],v['sha256']) for v in logical.values() if 'historical_source' in v}
 for p,h in baseline['present_inputs'].items():assert pins.get(p)==h or (p,h) in hist
 for p in candidate['absent_inputs']:assert not Path(p).exists() and not Path(p).is_symlink()
 prod=str(R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2dom.py')
 assert (prod,'ed95a235509219df22cf07aa59d732d249d724571a3537cb436359487136fc64') in hist
 assert pins[prod]=='4453ac9a3745b4525575945d0aab506f270bbbbbbcf52c09a160f6c60f2ecd38'
 assert all(not Path(p).is_relative_to(previous) for p,v in sources.items() if not v['external'])
 failed=Path('/tmp/k215-phase19-check/old-baseline-v3-run1');attempts=list((failed/'attempts').iterdir());assert len(attempts)==10
 for d in attempts:
  triple=[p for p in d.iterdir() if p.suffix in {'.lean','.log','.json'}];assert len(triple)==3 and all(str(p) in pins for p in triple)
 oldmeta=[failed/n for n in ['before.json','inventory.json','completed.json','toolchain.json']]+[Path('/tmp/k215-phase19-check')/n for n in ['old-baseline-v3-outer.json','old-baseline-v3.stdout','old-baseline-v3.stderr','old-plan.json','build-old.py','old-freeze.json']]
 assert all(str(p) in pins for p in oldmeta)
 olddone=read(failed/'completed.json');assert len(olddone)==223 and 'BusyBeaver.ZFC.L2Control219' not in olddone and not (failed/'result.json').exists()
 assert read('/tmp/k215-phase19-check/old-baseline-v3-outer.json')['exit_code']==1
 assert sum('/workspace/' in n for n in expected_raw)==452 and sum('/attempts/' in n for n in expected_raw)==84 and sum('/audits/' in n for n in expected_raw)==6
 for p,h in pins.items():assert digest(p)==h,p
 report={'status':'PASS_INDEPENDENT_ARCHIVE_INDEX_AND_REQUIRED_COVERAGE_REVIEW','auditor':pin(__file__),'archive':pin(archive),'index':pin(P/'index.json'),'capture_receipt':pin(P/'capture.json'),'config':pin(configpath),'raw_copy_plan':pin(cfg['raw_copy_plan']['source']),'blob_members':396,'logical_entries':713,'source_aliases':712,'external_boundary_files':11,'raw_files':562,'checked_workspace_sources':452,'accepted_fresh_attempt_triples':28,'candidate_audit_triples':2,'runtime_metadata_files':20,'context_rows':133,'failed_v3_attempt_triples_preserved':10,'failed_v3_metadata_files_preserved':10,'all_member_hashes_bytes_and_metadata_exact':True,'complete_logical_and_source_alias_index_reconstructed':True,'historical_producer_before_and_current_after_bound':True,'all_current_candidate_present_pins_checked':44,'all_required_absences_checked':8,'no_previous_packet_internal_aliases_copied':True,'objects_copied':False,'filesystem_archive_extraction':False,'archived_code_Lean_generator_or_capture_helper_execution':False,'scope':'Independent in-memory inspection of the root-created archive and exact alias reconstruction from approved config/raw sources. Does not execute captured helpers or extract files. Historical snapshots retain labels separately from current canonical byte providers.'}
 output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'review':pin(output)},indent=2))
if __name__=='__main__':main()
