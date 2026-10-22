#!/usr/bin/env python3
"""Capture reviewed phase17 evidence as deterministic blobs plus an alias index.

Reads explicitly pinned data only. Does not execute proof tools, generators,
archive readers or captured helpers. Requires a new destination directory.
"""
from pathlib import Path, PurePosixPath
from io import BytesIO
import argparse, gzip, hashlib, json, re, tarfile

R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification'
ANCESTORS=[P/'phase15/lean',P/'phase16/lean']
FORBIDDEN={'.olean','.ilean','.o','.obj','.a','.so','.dylib','.dll','.exe'}

def sha(data):return hashlib.sha256(data).hexdigest()
def load(path):return json.loads(Path(path).read_text())
def dump(value):return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
def pin(path,expected):
    assert isinstance(expected,str)and re.fullmatch('[0-9a-f]{64}',expected)
    path=Path(path);assert path.is_absolute()and '..'not in path.parts and path.is_file()and not path.is_symlink(),str(path)
    data=path.read_bytes();assert sha(data)==expected,str(path)
    return data
def safe(name):
    assert isinstance(name,str)and name and '\\'not in name and '\x00'not in name
    p=PurePosixPath(name);assert not p.is_absolute()and '..'not in p.parts and str(p)==name
    assert p.suffix not in FORBIDDEN and 'objects'not in p.parts
    return name
def ancestor(path):return any(Path(path).is_relative_to(root)for root in ANCESTORS)

def main():
    a=argparse.ArgumentParser();a.add_argument('--config',type=Path,required=True);a.add_argument('--out',type=Path,required=True);args=a.parse_args()
    config_path=args.config.resolve();config_bytes=config_path.read_bytes();cfg=json.loads(config_bytes)
    assert cfg['status']=='FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS'
    helper=Path(__file__).resolve();assert sha(helper.read_bytes())==cfg['capture_helper_sha256']
    out=args.out.absolute();assert not out.exists()and not out.is_symlink()
    plan=json.loads(pin(cfg['frozen_plan']['source'],cfg['frozen_plan']['sha256']))
    review=json.loads(pin(cfg['actual_review']['source'],cfg['actual_review']['sha256']))
    rawplan=json.loads(pin(cfg['raw_copy_plan']['source'],cfg['raw_copy_plan']['sha256']))
    assert review['status']=='PASS_READ_ONLY_ACTUAL_EVIDENCE_REVIEW'
    assert review['provider_count']==213 and review['fresh_providers']==171 and review['source_transitive_reuses']==42
    assert review['typed_clients']==14 and review['client_and_audit_warnings']==0
    assert review['site_batches']==9 and review['site_outcomes']==6176
    assert review['additional_pins_postchecked']==54 and review['absences_postchecked']==7
    assert review['plan_sha256']==cfg['frozen_plan']['sha256']
    assert review['helper_sha256']==cfg['actual_review_helper']['sha256']
    assert rawplan['status']=='DRAFT_COPY_PLAN_NO_MUTATION' and review['copy_plan_files']==len(rawplan['files'])==743
    assert len(plan['present_inputs'])==len(cfg['present_aliases'])==54
    assert set(plan['present_inputs'])==set(cfg['present_aliases'])
    boundaries={r['source']:r for r in cfg['external_boundaries']}
    assert len(boundaries)==len(cfg['external_boundaries'])
    expected_boundaries={p for p in plan['present_inputs']if ancestor(p)}
    assert set(boundaries)==expected_boundaries
    assert len(cfg['local_before'])==10
    logical={};sources={};blobs={};bindings={};external={}
    def bind(source,expected,name,role,is_external=False):
        name=safe(name);assert name not in logical,('duplicate logical name',name)
        source=Path(source);assert not source.is_relative_to(out)
        assert source.suffix not in FORBIDDEN and 'objects'not in source.parts
        if is_external:assert ancestor(source)
        else:
            assert not ancestor(source),('Ancestor packets stay external',str(source))
            assert not str(source).endswith(('.tar','.tar.gz','.tgz','.zip'))
        data=pin(source,expected);h=sha(data);bindings[str(source)]=h
        row={'source':str(source),'sha256':h,'bytes':len(data),'role':role}
        if is_external:row['external']=True;external[str(source)]=h
        else:row['blob']='blobs/'+h;blobs[h]=data
        logical[name]=row
        alias=sources.setdefault(str(source),{'sha256':h,'bytes':len(data),'external':is_external,'logical':[]})
        assert(alias['sha256'],alias['bytes'],alias['external'])==(h,len(data),is_external)
        alias['logical'].append(name)
    for row in rawplan['files']:
        assert row['bytes']>0 or Path(row['source']).stat().st_size==0
        bind(row['source'],row['sha256'],'runtime/'+safe(row['destination']),'actual_source_log_record')
        assert logical['runtime/'+row['destination']]['bytes']==row['bytes']
    for source,expected in plan['present_inputs'].items():
        name=cfg['present_aliases'][source]
        if source in boundaries:
            row=boundaries[source];assert row['sha256']==expected and row['logical']==name
            bind(source,expected,name,'frozen_ancestor_boundary',True)
        else:bind(source,expected,name,'frozen_present_input')
    for row in cfg['local_before']:bind(row['source'],row['sha256'],row['logical'],'local_cleanup_before')
    for row in cfg['files']:bind(row['source'],row['sha256'],row['logical'],row['role'])
    for key,name in [('actual_review','capture/actual-review.json'),('raw_copy_plan','capture/raw-copy-plan.json'),('frozen_plan','capture/frozen-plan.json'),('actual_review_helper','capture/review_actual.py')]:
        row=cfg[key];bind(row['source'],row['sha256'],name,key)
    bind(helper,cfg['capture_helper_sha256'],'capture/capture.py','owned_capture_helper')
    bind(config_path,sha(config_bytes),'capture/config.json','owned_capture_config')
    # Exactly ten local snapshots must match the reviewed adoption's before hashes.
    assert plan['present_inputs'][cfg['local_adoption']['source']]==cfg['local_adoption']['sha256']
    adoption=json.loads(pin(cfg['local_adoption']['source'],cfg['local_adoption']['sha256']))
    expected={r['path']:r['before_sha256']for r in adoption['files']}
    assert len(expected)==10 and {r['repo_path']:r['sha256']for r in cfg['local_before']}==expected
    for p in plan['absent_inputs']:assert not Path(p).exists()and not Path(p).is_symlink()
    out.mkdir(parents=True,exist_ok=False);archive=out/'evidence.tar.gz'
    with archive.open('xb')as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)as gz:
            with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT)as tar:
                for h,data in sorted(blobs.items()):
                    info=tarfile.TarInfo('blobs/'+h);info.size=len(data);info.mode=0o644;info.uid=info.gid=0;info.mtime=0;info.uname=info.gname=''
                    tar.addfile(info,BytesIO(data))
    # Validate the created archive directly; never extract or execute members.
    with tarfile.open(archive,'r:gz')as tar:
        members=tar.getmembers();assert len(members)==len(blobs)
        assert {m.name for m in members}=={'blobs/'+h for h in blobs}
        assert len({m.name for m in members})==len(members)
        for member in members:
            assert member.isfile()and not member.issym()and not member.islnk()and safe(member.name)==member.name
            assert member.uid==member.gid==member.mtime==0 and member.mode==0o644
            data=tar.extractfile(member).read();assert data==blobs[member.name[6:]] and sha(data)==member.name[6:] and member.size==len(data)
    for source,h in bindings.items():assert sha(Path(source).read_bytes())==h
    for p in plan['absent_inputs']:assert not Path(p).exists()and not Path(p).is_symlink()
    for row in sources.values():row['logical'].sort()
    index={'format':'phase17-explicit-evidence-blobs-v1','archive_sha256':sha(archive.read_bytes()),'logical':dict(sorted(logical.items())),'sources':dict(sorted(sources.items())),'external_boundaries':dict(sorted(external.items())),'raw_statuses':'Original file bytes preserved; source-review pending statuses are historical data, not rewritten.','scope':'Source/raw compiler evidence capture only; no replay or proof execution. Ancestor packets remain exact named external boundaries.'}
    (out/'index.json').write_bytes(dump(index))
    receipt={'status':'PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION','archive_sha256':index['archive_sha256'],'archive_bytes':archive.stat().st_size,'index_sha256':sha((out/'index.json').read_bytes()),'logical_entries':len(logical),'source_aliases':len(sources),'blob_members':len(blobs),'blob_bytes':sum(map(len,blobs.values())),'external_boundary_files':len(external),'raw_plan_files':743,'frozen_present_inputs':54,'local_before_snapshots':10,'capture_helper_sha256':cfg['capture_helper_sha256'],'config_sha256':sha(config_path.read_bytes()),'actual_review_sha256':cfg['actual_review']['sha256'],'compiler_execution':False,'supplied_code_execution':False,'objects_copied':False}
    (out/'capture.json').write_bytes(dump(receipt));print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
