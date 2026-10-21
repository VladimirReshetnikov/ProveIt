"""Validate the exact local phase6 packet and its referenced ancestry in place.

Imports only hash-pinned local validators. No archived source is executed and
no earlier archive is copied into the new packet.
"""
from pathlib import Path
import hashlib, importlib.util, json, sys
HERE = Path(__file__).resolve().parent
REFERENCE_SHA256 = 'b7f8e223fd6b8e6cd55a6b35ab006f9d859dde10c4e81c0f1d62b5fcd0cde152'
sha = lambda data: hashlib.sha256(data).hexdigest()

def reference(data=None):
    data = (HERE/'basis-reference.json').read_bytes() if data is None else data
    assert sha(data) == REFERENCE_SHA256
    return json.loads(data)

def locate(repo=None):
    ref=reference()
    for root in ([Path(repo).resolve()] if repo is not None else list(HERE.parents)):
        packet=root/ref['repository_relative_directory']
        if packet.is_dir(): return root,packet
    raise AssertionError('Exact phase6 packet missing; provide --basis-repo /path/to/Proofs')

def pinned_files(repo=None,supplied_reference=None):
    ref=reference(supplied_reference);root,packet=locate(repo);files={}
    for name,pin in ref['files'].items():
        path=packet/name
        assert path.is_file() and not path.is_symlink()
        data=path.read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
        files[name]=data
    return packet,files,ref

def validate(repo=None,supplied_reference=None):
    packet,files,ref=pinned_files(repo,supplied_reference)
    # Pin every local import before loading it; restore the caller's modules.
    modules=(('basis_reference','basis_reference.py'),('evidence','evidence.py'),
             ('_phase6_pinned_saved','review_saved.py'))
    saved={n:sys.modules.get(n) for n,_ in modules}
    try:
        for name,filename in modules:
            spec=importlib.util.spec_from_file_location(name,packet/filename)
            module=importlib.util.module_from_spec(spec);sys.modules[name]=module
            spec.loader.exec_module(module)
        reader=sys.modules['_phase6_pinned_saved']
        checked=reader.review(packet,basis_repo=repo)
        assert checked['status']=='PASS_SAVED_EVIDENCE_REVIEW'
        index=json.loads(files['index.json'])
        members=reader.read_members(packet/'execution.tar.gz',index)
        assert sha(members['execution/result.json'])==ref['raw_result_sha256']
        assert members['review/live-review.json']==files['live-review.json']
        assert pinned_files(repo,supplied_reference)[1]==files
        return members,checked,files
    finally:
        for name,value in saved.items():
            if value is None:sys.modules.pop(name,None)
            else:sys.modules[name]=value
