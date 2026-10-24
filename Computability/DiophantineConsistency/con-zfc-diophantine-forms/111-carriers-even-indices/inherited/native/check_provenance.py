#!/usr/bin/env python3
"""Check identities of pinned inherited texts, not their mathematical semantics."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent

def main():
    ledger=json.loads((HERE/'PROVENANCE.json').read_text())
    total=0
    for entry in ledger['files']:
        data=(HERE/entry['file']).read_bytes()
        if len(data)!=entry['bytes']:
            raise ValueError('byte count: '+entry['file'])
        if hashlib.sha256(data).hexdigest()!=entry['sha256']:
            raise ValueError('SHA-256: '+entry['file'])
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob!=entry['git_blob_sha1']:
            raise ValueError('Git blob: '+entry['file'])
        if 'earlier_source_pin' in entry:
            if not(entry['matches_earlier_sha256'] and entry['matches_earlier_git_blob']):
                raise ValueError('earlier pin mismatch: '+entry['file'])
        total+=len(data)
    print(json.dumps({'status':'PASS','files':len(ledger['files']),'bytes':total,
        'scope':'Exact inherited file identities only; no new verification of unbounded calibration.'},indent=2))

if __name__=='__main__':
    main()
