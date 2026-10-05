#!/usr/bin/env python3
"""Validate the declared release before creating build outputs."""
from pathlib import Path
import hashlib,json,re,sys
REQUIRED = ('PROVENANCE.json', 'README.md', 'VERIFICATION.md', 'build.sh', 'checks/formal/README.md', 'checks/formal/data/endpoint_9.json', 'checks/formal/data/formal_9.json', 'checks/formal/data/formal_9_linear_solver.json', 'checks/formal/diagnostics/README.md', 'checks/formal/diagnostics/exact_dp_3000.json', 'checks/formal/diagnostics/numerical_analysis.json', 'checks/formal/formal_engine.py', 'checks/formal/manifest.json', 'checks/formal/negative_tests.py', 'checks/formal/provenance/source_hashes.json', 'checks/formal/requirements.txt', 'checks/formal/verify.py', 'checks/verify_compacted.py', 'compacted_tree_amplitude.pdf', 'compacted_tree_amplitude.tex', 'dependencies/relaxed_tree_amplitude.pdf', 'dependencies/relaxed_tree_amplitude_sources.zip', 'numerics/README.md', 'numerics/compute_canonical_amplitude.py', 'numerics/compute_canonical_amplitude.txt', 'replay.sh', 'verify_release.py')
class VerificationError(RuntimeError): pass
def require(test,label):
    if not test: raise VerificationError(label)
def unique(pairs):
    result={}
    for k,v in pairs:
        require(k not in result,'duplicate manifest key')
        result[k]=v
    return result
def verify(root):
    data=json.loads((root/'MANIFEST.json').read_text(),object_pairs_hook=unique)
    require(type(data) is dict and set(data)=={'schema','algorithm','files'},'manifest schema')
    require(type(data['schema']) is int and data['schema']==1 and data['algorithm']=='sha256','manifest version')
    require(type(data['files']) is dict and set(data['files'])==set(REQUIRED),'exact release inventory')
    for name in REQUIRED:
        record=data['files'][name]
        require(type(record) is dict and set(record)=={'bytes','sha256'},'manifest entry shape')
        require(type(record['bytes']) is int and record['bytes']>=0,'manifest byte count')
        require(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None,'manifest hash syntax')
        path=root/name
        require(path.is_file() and not path.is_symlink(),'missing or symlinked source '+name)
        parent=path.parent
        while parent!=root:
            require(not parent.is_symlink(),'symlinked source parent')
            parent=parent.parent
        content=path.read_bytes()
        require(len(content)==record['bytes'],'byte count mismatch '+name)
        require(hashlib.sha256(content).hexdigest()==record['sha256'],'SHA-256 mismatch '+name)
    print('PASS release integrity: '+str(len(REQUIRED))+' required files, sizes, SHA-256, no symlinked sources')
if __name__=='__main__':
    try:
        require(len(sys.argv)==1,'no options accepted; full coverage is mandatory')
        verify(Path(__file__).resolve().parent)
    except (VerificationError,OSError,ValueError) as error:
        print('FAIL: '+str(error),file=sys.stderr);sys.exit(1)
