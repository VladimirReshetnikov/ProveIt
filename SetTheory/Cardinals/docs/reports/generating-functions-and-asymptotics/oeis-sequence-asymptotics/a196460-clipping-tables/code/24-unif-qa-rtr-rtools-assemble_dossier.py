#!/usr/bin/env python3
"""Package compact review evidence; hash all external tests, never execute retained code."""
import hashlib,json,os,shutil,stat
from pathlib import Path
D=Path('/workspace/shared/oeis-uniform-sectors-tools-review-20261004')
R=Path('/workspace/shared/oeis-uniform-sectors-release-20261004')
Q=D/'qa-copy'
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(v):return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def row(p):
 s=p.lstat();d={'kind':'directory' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'symlink' if stat.S_ISLNK(s.st_mode) else 'other','mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
 if d['kind']=='file':b=p.read_bytes();d.update(size=len(b),sha256=sha(b))
 elif d['kind']=='symlink':d['target']=os.readlink(p)
 return d
def cp(source,target):
 target=Q/target;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
 need(source.read_bytes()==target.read_bytes(),'evidence copy changed')
need(not Q.exists(),'fresh compact dossier required')
original=json.loads((D/'evidence/INDEPENDENT_ORIGINAL_BOUNDARY.json').read_bytes())
current={p:row(Path(p)) for p in original}
need(current==original,'originals changed during independent review')
for name,value in current.items():
 if value['kind']=='directory':need(all(str(p) in current for p in Path(name).rglob('*')),'new descendant in original boundary')
(D/'evidence/FINAL_ORIGINALS_PRESERVATION.json').write_bytes(enc({'status':'PASS','scoped_original_entries':355,'independent_before_equals_final_after':True,'objects':current,'atime_ctime_owner_inode_directory_allocation_excluded':True}))
replay=json.loads((D/'evidence/INDEPENDENT_REPLAY_RECEIPT.json').read_bytes())
for name,pin in replay['artifact_pins'].items():need(sha((R/name).read_bytes())==pin,'final artifact pin changed')
need(sha((R/'tools/README.md').read_bytes())=='f29b0697161437a3e1c3a39781d6e957e67312944a50d072ba7faa7a57496f9e','final tool documentation pin')
coordinator=Path('/workspace/shared/oeis_uniform_finalize_release_20261004.py')
need(sha(coordinator.read_bytes())=='084a3ab0ff2ca4f80cf4f7589fadbc2e2c62bb31af7d1a734e6570c6b05e72c7','final coordinator pin')
Q.mkdir()
cp(D/'REVIEW.md','REVIEW.md')
for p in sorted((R/'tools').iterdir()):
 need(p.is_file(),'unexpected current tool directory');cp(p,'reviewed-tools/'+p.name)
for name in ['audit_preservation.py','hostile_tests.py','audit_replay.py','assemble_dossier.py']:cp(D/name,'reviewer-tools/'+name)
cp(coordinator,'reviewer-tools/'+coordinator.name)
for p in sorted((D/'evidence').iterdir()):cp(p,'evidence/'+p.name)
cp(D/'candidate-manifest.json','evidence/REVIEW_CANDIDATE_MANIFEST.json')
for category,folder,receipt in [('owned-tests','owned-selftests','SELFTEST_RECEIPT.json'),('independent-hostile-tests','independent-hostile-tests','INDEPENDENT_HOSTILE_RECEIPT.json')]:
 cp(D/folder/receipt,category+'/'+receipt)
 for p in sorted((D/folder).glob('*.stdout')):cp(p,category+'/logs/'+p.name)
for category,folder in [('candidate-replay','candidate-replay'),('relocated-replay','relocated-replay'),('synthetic-bootstrap','owned-selftests/bootstrap'),('synthetic-locked','owned-selftests/locked'),('synthetic-relocated','owned-selftests/relocated-build')]:
 for p in sorted((D/folder).iterdir()):
  if p.is_file() and p.suffix in {'.json','.fls','.stdout','.log','.txt'}:cp(p,'replays/'+category+'/'+p.name)
for p in sorted((D/'independent-hostile-tests/extra-system-output').iterdir()):
 if p.is_file():cp(p,'independent-hostile-tests/extra-system-failure/'+p.name)
external={}
for p in sorted(D.rglob('*')):
 if p==Q or Q in p.parents:continue
 external[p.relative_to(D).as_posix()]=row(p)
external_receipt={'format':'Uniform sectors external review evidence inventory v1','base':str(D),'excludes':['qa-copy subtree','external root metadata'],'objects':external,'scientific_code_in_fixtures_is_inert':True}
(Q/'EXTERNAL_EVIDENCE_INVENTORY.json').write_bytes(enc(external_receipt))
toolpins={p.name:sha(p.read_bytes()) for p in sorted((Q/'reviewed-tools').iterdir())}
receipt={'status':'PASS','scope':'Independent presentation tools and source preservation review; stable v2 article replay and pre-final-QA candidate ZIP roundtrip. Does not certify final root seal or post-seal delivery gate.','artifact_pins':replay['artifact_pins'],'reviewed_tools_sha256':toolpins,'source_proof_sha256':'ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65','independent_audit_sha256':'4fa84b2ddfe383668c86ea0ad4d7419b0304eb0d9a97725aecbdab7e3b63ff03','original_objects_preserved':355,'frozen_files':213,'frozen_directories':26,'historical_source_objects':51,'historical_audit_objects':333,'predecessor_unchanged':True,'fresh_owned_test_count':39,'independent_extra_hostile_test_count':19,'exact_article_replays':2,'article_pages':12,'system_input_lock_count':190,'executable_lock_count':7,'recorder_passes_per_build':4,'deterministic_candidate_zip_sha256':replay['review_candidate_zip_sha256'],'review_candidate_manifest_sha256':replay['review_candidate_manifest_sha256'],'final_coordinator_sha256':sha(coordinator.read_bytes()),'final_coordinator_static_review':'PASS, not executed by independent reviewer','model_performed_review':True,'no_scientific_execution_or_import':True,'original_release_not_modified_by_reviewer':True,'documentation_post_snapshot_correction':'tools/README Human -> Visual; exact final documentation is pinned in reviewed tools','external_evidence_inventory_sha256':sha((Q/'EXTERNAL_EVIDENCE_INVENTORY.json').read_bytes()),'external_evidence_objects':len(external),'qa_copy_eligible_boundary':'Entire qa-copy directory including REVIEW_MANIFEST.json; root directory and manifest self-metadata excluded from its manifest','review_manifest_format':'Uniform sectors independent release-tools review dossier v1','root_final_seal_and_post_seal_gate_pending':True}
(Q/'REVIEW_RECEIPT.json').write_bytes(enc(receipt))
for p in sorted(Q.rglob('*'),key=lambda p:(-len(p.parts),str(p))):p.chmod(0o555 if p.is_dir() else 0o444)
files,dirs={},{}
for p in sorted(Q.rglob('*')):
 x=row(p);n=p.relative_to(Q).as_posix();r={'mode':x['mode'],'mtime_ns':x['mtime_ns']}
 if x['kind']=='directory':dirs[n]=r
 else:need(x['kind']=='file','unexpected compact symlink');files[n]={**r,'bytes':x['size'],'sha256':x['sha256']}
manifest={'format':'Uniform sectors independent release-tools review dossier v1','files':files,'directories':dirs}
raw=enc(manifest);m=Q/'REVIEW_MANIFEST.json';m.write_bytes(raw);m.chmod(0o444);Q.chmod(0o555)
for name,r in files.items():
 x=row(Q/name);need(r=={'mode':x['mode'],'mtime_ns':x['mtime_ns'],'bytes':x['size'],'sha256':x['sha256']},'compact manifest row differs')
for name,r in dirs.items():x=row(Q/name);need(r=={'mode':x['mode'],'mtime_ns':x['mtime_ns']},'compact directory differs')
print(json.dumps({'status':'PASS','qa_copy':str(Q),'review_manifest_sha256':sha(raw),'files_excluding_manifest':len(files),'directories_excluding_root':len(dirs),'bytes_excluding_manifest':sum(r['bytes'] for r in files.values()),'external_objects':len(external)},indent=2))
