#!/usr/bin/env python3
"""Check the shipped K230 snapshot against its exact upstream CI receipts.

This verifies provenance and recorded results, not a local Rocq rebuild.
The original ZIP is retained and every extracted byte is compared with it.
"""
from pathlib import Path
import hashlib, json, sys, zipfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import build

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def audit():
    repo=ROOT/'vendor/k230-rocq'; ci=ROOT/'evidence/upstream-ci'
    manifest=json.loads((repo/'manifest.json').read_text())
    md=sha(repo/'manifest.json')
    build.require(md == build.PINS['vendor/k230-rocq/manifest.json'], 'Wrong manifest')
    checked=0
    for name,digest in manifest['local_files'].items():
        build.require(sha(repo/name)==digest,'Local upstream source hash mismatch: '+name)
        checked+=1
    archive=ROOT/'evidence/upstream-ci-original.zip'
    build.require(sha(archive)=='60702d530e637fd343eda4d370b73d71924ca5c3f581444196acdf5da344f15f','Wrong CI artifact bytes')
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            if info.is_dir(): continue
            name=Path(info.filename).name
            build.require(z.read(info.filename)==(ci/name).read_bytes(),'Extracted CI file differs: '+name)
    result=json.loads((ci/'verification-result.json').read_text())
    chk=json.loads((ci/'coqchk-result.json').read_text())
    build.require(result['status']=='PASSED' and result['manifest_sha256']==md,'CI manifest/result mismatch')
    build.require(result['machine_sha256']==sha(repo/'machine/k230.tm'),'CI machine mismatch')
    build.require(result['reference_commit']=='c132d7eae8158cd3a9850ea3eb7251158c3dd821','CI dependency mismatch')
    build.require(len(result['compiled'])==216 and result['closed_reports']==2,'CI coverage mismatch')
    build.require(chk['status']=='PASSED' and chk['exit_code']==0 and result['coqchk']==chk,'CI kernel-check mismatch')
    build.require(chk['log_sha256']==sha(ci/'coqchk.log'),'Kernel-check log differs')
    return {'status':'PINNED_UPSTREAM_RECEIPT_AUDIT_PASS','local_manifest_entries':checked,
            'compiled_source_count':len(result['compiled']),'closed_endpoint_reports':result['closed_reports'],
            'upstream_repository_commit':'3142e4dd980f0be12f4abb636c4ae2528afc17eb',
            'workflow_url':'https://github.com/elliotglazer/k230-rocq/actions/runs/39258562285',
            'artifact_id':12192455062,'manifest_sha256':md,'artifact_sha256':sha(archive),
            'coqchk_exit_code':chk['exit_code'],
            'scope':'Authentic pinned upstream source and CI evidence checked locally. No local Rocq rebuild and no new reduced-table Rocq endpoint.'}

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
