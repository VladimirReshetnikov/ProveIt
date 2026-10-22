"""Owned independent direct tar/index read; no extraction or captured-code execution."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,re,tarfile
D=Path(__file__).resolve().parent;P=Path('/tmp/k215-phase17-published/lean');C=Path('/tmp/k215-phase17-publication/config.final-v2.json')
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(Path(p).read_text())
assert sha(C.read_bytes())=='23e0a134fa025c17390568d6dcc2e62129b5f14e745a636499b7ce81e7d569c9'
cfg=read(C);idx=read(P/'index.json');receipt=read(P/'capture.json');plan=read(cfg['frozen_plan']['source']);raw=read(cfg['raw_copy_plan']['source']);expected={}
def add(name,source,pin,role,external=False):
 assert name not in expected
 expected[name]={'source':source,'sha256':pin,'role':role,'external':external}
for row in raw['files']:add('runtime/'+row['destination'],row['source'],row['sha256'],'actual_source_log_record')
external={r['source']:r for r in cfg['external_boundaries']}
for source,pin in plan['present_inputs'].items():add(cfg['present_aliases'][source],source,pin,'frozen_ancestor_boundary'if source in external else'frozen_present_input',source in external)
for row in cfg['local_before']:add(row['logical'],row['source'],row['sha256'],'local_cleanup_before')
for row in cfg['files']:add(row['logical'],row['source'],row['sha256'],row['role'])
for key,name in [('actual_review','capture/actual-review.json'),('raw_copy_plan','capture/raw-copy-plan.json'),('frozen_plan','capture/frozen-plan.json'),('actual_review_helper','capture/review_actual.py')]:
 row=cfg[key];add(name,row['source'],row['sha256'],key)
helper=Path('/tmp/k215-phase17-publication/capture.py');add('capture/capture.py',str(helper),sha(helper.read_bytes()),'owned_capture_helper');add('capture/config.json',str(C),sha(C.read_bytes()),'owned_capture_config')
assert len(expected)==len(idx['logical'])==905 and set(expected)==set(idx['logical'])
assert idx['format']=='phase17-explicit-evidence-blobs-v1'
assert sha((P/'evidence.tar.gz').read_bytes())==idx['archive_sha256']==receipt['archive_sha256']=='5aa2c1f9a0ca891cb1427400c43d4a638ac3ad78f7abdd5a193e4b009e50270d'
assert sha((P/'index.json').read_bytes())==receipt['index_sha256']=='6f07704404bacddac73416525e16e72e5a1c6a2c754b6ec514552c24c62acc88'
assert receipt['status']=='PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION'
assert receipt['config_sha256']==sha(C.read_bytes())and receipt['capture_helper_sha256']==sha(helper.read_bytes())
blobs={}
with tarfile.open(P/'evidence.tar.gz','r:gz')as tar:
 members=tar.getmembers();names=[m.name for m in members];assert names==sorted(names)and len(set(names))==len(names)==579
 for member in members:
  assert re.fullmatch('blobs/[0-9a-f]{64}',member.name)and member.isfile()and not member.issym()and not member.islnk()
  assert member.uid==member.gid==member.mtime==0 and member.mode==0o644 and member.uname==member.gname==''
  b=tar.extractfile(member).read();assert len(b)==member.size and sha(b)==member.name[6:];blobs[member.name]=b
assert sum(map(len,blobs.values()))==receipt['blob_bytes']==8394375
sources={};boundaries={};used=set()
for name,wanted in expected.items():
 row=idx['logical'][name];assert (row['source'],row['sha256'],row['role'],row.get('external',False))==(wanted['source'],wanted['sha256'],wanted['role'],wanted['external'])
 b=Path(row['source']).read_bytes();assert sha(b)==row['sha256']and len(b)==row['bytes']
 if wanted['external']:
  assert 'blob'not in row;boundaries[row['source']]=row['sha256']
 else:
  assert row['blob']=='blobs/'+row['sha256']and blobs[row['blob']]==b;used.add(row['blob'])
 source=sources.setdefault(row['source'],{'sha256':row['sha256'],'bytes':len(b),'external':wanted['external'],'logical':[]})
 assert (source['sha256'],source['bytes'],source['external'])==(row['sha256'],len(b),wanted['external']);source['logical'].append(name)
for row in sources.values():row['logical'].sort()
assert sources==idx['sources']and len(sources)==receipt['source_aliases']==891
assert used==set(blobs)and boundaries==idx['external_boundaries']and len(boundaries)==16
assert (P/'evidence.tar.gz').stat().st_size==receipt['archive_bytes']==1662882
assert receipt['logical_entries']==905 and receipt['blob_members']==579 and receipt['raw_plan_files']==743 and receipt['frozen_present_inputs']==54 and receipt['local_before_snapshots']==10
assert receipt['compiler_execution']is False and receipt['supplied_code_execution']is False and receipt['objects_copied']is False
def data(name):return blobs[idx['logical'][name]['blob']]
assert json.loads(data('history/initial-policy-stop/build-outer.json'))['status']=='FAIL'
assert json.loads(data('history/initial-policy-stop/attempt137/record.json'))['status']=='PASS'
assert json.loads(data('history/actual-review/failure/outer.json'))['status']=='FAIL'
assert b'NotADirectoryError'in data('history/actual-review/failure/stderr')
assert json.loads(data('context/actual-review/pass/outer.json'))['status']=='PASS_EXIT_ZERO'
actual=json.loads(data('capture/actual-review.json'));assert actual['status']=='PASS_READ_ONLY_ACTUAL_EVIDENCE_REVIEW'and actual['profile_exception']['after']==['propext']and actual['profile_exception']['original_status']=='FAIL'
assert json.loads(data('capture/config.json'))==cfg
result={'status':'PASS_INDEPENDENT_DIRECT_CAPTURE_READ','archive_sha256':idx['archive_sha256'],'archive_bytes':1662882,'index_sha256':sha((P/'index.json').read_bytes()),'capture_receipt_sha256':sha((P/'capture.json').read_bytes()),'final_config_sha256':sha(C.read_bytes()),'prior_source_map_review_sha256':sha((D/'resumed-config-review.json').read_bytes()),'logical_entries_checked':905,'source_aliases_checked':891,'regular_blob_members_checked':579,'blob_bytes_checked':8394375,'external_boundary_files_hash_checked':16,'raw_subset_files':743,'before_snapshots':10,'context_files':92,'all_configured_aliases_exact_and_complete':True,'all_actual_source_bytes_equal_captured_blobs':True,'all_tar_member_names_metadata_types_sizes_hashes_checked':True,'original_policy_and_metadata_failures_retained_verbatim':True,'new_actual_review_and_profile_exception_bound':True,'archive_extracted':False,'captured_helpers_or_compiler_executed':False,'objects_included':False,'own_reader_sha256':sha(Path(__file__).read_bytes())}
(D/'actual-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
