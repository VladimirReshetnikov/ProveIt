"""Verify exact delivered bytes and primary pins; standard library only."""
from hashlib import sha256
import gzip
import json
import os
from pathlib import Path

ROOT=Path(__file__).resolve().parent
CORE='42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'
COMPILER='f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f'
SOURCE='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'

def require(ok,detail):
    if not ok:raise RuntimeError(detail)

def verify():
    raw=(ROOT/'release-manifest.json').read_bytes()
    require(sha256(raw).hexdigest()==(ROOT/'release-manifest.json.sha256').read_text().split()[0],'manifest digest')
    manifest=json.loads(raw)
    expected=set(manifest['files'])|{'release-manifest.json','release-manifest.json.sha256'}
    # Only these documented generated trees may contain unmanifested files.
    generated={'.build','replay-output'}
    observed=set()
    for directory,dirs,files in os.walk(ROOT,followlinks=False):
        base=Path(directory)
        for item in dirs+files:
            require(not (base/item).is_symlink(),'symlink in release tree: '+str((base/item).relative_to(ROOT)))
        for name in files:
            relative=(base/name).relative_to(ROOT)
            if relative.parts[0] not in generated:observed.add(relative.as_posix())
        for name in dirs:
            relative=(base/name).relative_to(ROOT)
            if relative.parts[0] not in generated:
                prefix=relative.as_posix()+'/'
                require(any(x.startswith(prefix) for x in expected),'unexpected directory: '+relative.as_posix())
    require(observed==expected,'inventory mismatch; extra='+str(sorted(observed-expected))+' missing='+str(sorted(expected-observed)))
    for name,entry in manifest['files'].items():
        relative=Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,'invalid manifest path')
        p=ROOT/relative
        require(p.is_file() and not p.is_symlink(),'missing or symlinked file: '+name)
        data=p.read_bytes()
        require(len(data)==entry['bytes'] and sha256(data).hexdigest()==entry['sha256'],'file mismatch: '+name)
    base=ROOT/'reproducibility'
    for name,digest in [('lazy_reversible.py',CORE),('frozen_reversible_binary.py',COMPILER)]:
        require(sha256((base/name).read_bytes()).hexdigest()==digest,'primary pin: '+name)
    data=gzip.decompress((base/'source.json.gz').read_bytes())
    require(len(data)==32034272 and sha256(data).hexdigest()==SOURCE,'uncompressed source pin')
    for directory in ('evidence','portable-replay/normal','portable-replay/optimized'):
        for p in (base/directory).glob('*receipt*.json'):
            record=json.loads(p.read_text())
            require(record['status']=='passed','receipt status: '+p.name)
            value=record.get('evaluator_sha256',record.get('lazy_sha256'))
            require(value==CORE,'receipt core linkage: '+p.name)
    return dict(status='passed',files_verified=len(manifest['files']),evaluator_sha256=CORE,compiler_sha256=COMPILER,source_sha256=SOURCE)

if __name__=='__main__':print(json.dumps(verify(),indent=2))
