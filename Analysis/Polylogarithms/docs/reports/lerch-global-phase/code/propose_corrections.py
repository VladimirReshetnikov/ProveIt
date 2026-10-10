#!/usr/bin/env python3
"""Print a guarded local diff; write only with an explicit --apply flag.

No network requests or Git operations are performed. An unexpected source
blob causes failure instead of applying edits to unseen manuscript changes.
"""
from __future__ import annotations
import argparse,difflib,hashlib,json
from pathlib import Path

def git_blob_sha(data:bytes)->str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def main()->None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True,help='local ProveIt checkout root')
    p.add_argument('--apply',action='store_true',help='explicitly write the two local corrections')
    a=p.parse_args()
    spec_path=Path(__file__).resolve().parents[1]/'integration'/'corrections.json'
    spec=json.loads(spec_path.read_text())
    target=a.repo/spec['repository_path']
    raw=target.read_bytes()
    actual=git_blob_sha(raw)
    if actual!=spec['expected_git_blob_sha1']:
        raise SystemExit('Baseline mismatch: expected '+spec['expected_git_blob_sha1']+'; got '+actual+'. No file changed.')
    old=raw.decode('utf-8');new=old
    for edit in spec['edits']:
        if new.count(edit['old'])!=1:
            raise SystemExit('Replacement is not unique: '+edit['id']+'. No file changed.')
        new=new.replace(edit['old'],edit['new'],1)
    print(''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),
                    fromfile='a/'+spec['repository_path'],tofile='b/'+spec['repository_path'])),end='')
    if a.apply:target.write_bytes(new.encode('utf-8'))
if __name__=='__main__':main()
