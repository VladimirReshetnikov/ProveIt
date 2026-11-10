"""Read-only verification of the distributed package and finite evidence."""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result)
    return result

def main():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for row in manifest['files']:
        data=(ROOT/row['path']).read_bytes()
        if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:
            raise ValueError('Changed distributed artifact: '+row['path'])
    print('Verified',len(manifest['files']),'payload identities.')
    measure=load_module('measure',ROOT/'measure.py')
    actual=measure.collect()
    expected=json.loads((ROOT/'evidence/checker_metrics.json').read_text())
    if actual!=expected:
        raise ValueError('Metrics differ; recorded runtime is '+expected['python']+', zlib '+expected['zlib_runtime'])
    for name in ['code/checker.py','code/readable_checker.py','ancillary/checker_bytes.py','ancillary/checker_ast.py']:
        path=ROOT/name
        if gzip.decompress(path.with_suffix('.py.gz').read_bytes())!=path.read_bytes():
            raise ValueError('Gzip source mismatch: '+name)
    print('Whole-source, matched-driver and gzip measurements verified.')
    result=load_module('verification',ROOT/'tests/verify.py').verify()
    print(json.dumps(result,indent=2))
    print('All distributed checks passed; written metatheorems are not machine formalized.')

if __name__=='__main__':
    main()
