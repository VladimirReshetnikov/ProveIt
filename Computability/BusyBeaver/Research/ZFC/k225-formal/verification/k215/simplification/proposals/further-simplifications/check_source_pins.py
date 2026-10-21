#!/usr/bin/env python3
"""Owned data-only source-pin and review-binding verification. No upstream code runs."""
import os, sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION')
import hashlib, json
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise SystemExit(message)

def load(path):return json.loads((ROOT/path).read_text())

def check_file(name,git=None,sha256=None,size=None):
    rel=PurePosixPath(name)
    require(not rel.is_absolute() and '..' not in rel.parts, 'UNSAFE_PIN_PATH')
    p=ROOT.joinpath(*rel.parts)
    require(p.is_file() and not p.is_symlink(), 'MISSING_PINNED_INPUT: '+name)
    data=p.read_bytes()
    got_git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    got_sha=hashlib.sha256(data).hexdigest()
    require(git is None or got_git==git,'GIT_BLOB_MISMATCH: '+name)
    require(sha256 is None or got_sha==sha256,'SOURCE_SHA256_MISMATCH: '+name)
    require(size is None or len(data)==size,'SOURCE_SIZE_MISMATCH: '+name)
    return {'path':name,'bytes':len(data),'sha256':got_sha,'git_blob':got_git,'git_blob_checked':git is not None}

def main():
    groups={}
    groups['recent_commits']=[]
    for pin in load('recent_commits/SOURCE_PINS.json'):
        remote=pin['path']
        if '/proposals/' in remote:rel=remote.split('/proposals/',1)[1]
        elif '/rocq-extension/coq/215/' in remote:rel='production/rocq/'+remote.rsplit('/',1)[1]
        else:rel='production/'+remote.rsplit('/',1)[1]
        groups['recent_commits'].append(check_file('recent_commits/sources/'+rel,git=pin['git_blob_sha']))
    groups['runtime_contexts']=[check_file('runtime_contexts/inputs/'+name,git=pin['git_blob'],sha256=pin['sha256'],size=pin['bytes']) for name,pin in load('runtime_contexts/INPUT_PINS.json')['files'].items()]
    groups['calibration']=[check_file('calibration/'+pin['local'],git=pin['sha'],sha256=pin['sha256'],size=pin['bytes']) for pin in load('calibration/SOURCE_PINS.json')['files']]
    groups['wellformedness']=[check_file('wellformedness/sources/'+pin.get('local_filename',Path(pin['path']).name),git=pin['sha']) for pin in load('wellformedness/SOURCE_PINS.json')['files']]
    pin=load('terminal_contract/SOURCE_PIN.json')
    groups['terminal_contract']=[check_file('terminal_contract/input/PositiveStutter.lean',git=pin['git_blob_sha'],sha256=pin['sha256'])]
    groups['phase5_refresh']=[check_file('recent_commits/phase5_refresh/'+pin['local'],git=pin['git_blob_sha'],sha256=pin['sha256'],size=pin['bytes']) for pin in load('recent_commits/phase5_refresh/SOURCE_PINS.json')]
    review=[check_file(name,sha256=digest) for name,digest in load('review/REVIEWED_SHA256.json').items()]
    report={'status':'PASS_BUNDLED_SOURCE_PINS_AND_REVIEW_BINDINGS','source_occurrences_checked':sum(map(len,groups.values())), 'distinct_source_sha256':len({x['sha256'] for g in groups.values() for x in g}), 'groups':groups,'review_bindings':review,'upstream_code_executed':False,'compilers_rerun':False}
    (ROOT/'SOURCE_PIN_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'source_occurrences_checked':report['source_occurrences_checked'],'review_bindings_checked':len(review)},indent=2))
if __name__=='__main__':main()
