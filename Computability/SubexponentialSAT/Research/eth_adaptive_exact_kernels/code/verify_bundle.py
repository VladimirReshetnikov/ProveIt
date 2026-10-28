"""Sealed-file and selected-source integrity, not mathematical verification."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent.parent
def verify(root=ROOT):
    count=0
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);p=root/name
        if not p.is_file():raise ValueError('missing sealed file: '+name)
        if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:raise ValueError('changed sealed file: '+name)
        count+=1
    manifest=json.loads((root/'sources/manifest.json').read_text())
    for row in manifest['selected_files']:
        if hashlib.sha256((root/row['file']).read_bytes()).hexdigest()!=row['sha256']:
            raise ValueError('selected source mismatch: '+row['file'])
    old=json.loads((root/'sources/prior/manifest.json').read_text())
    for row in old['files']:
        b=(root/'sources/prior'/row['file']).read_bytes()
        if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=row['blob']:
            raise ValueError('source Git blob mismatch: '+row['file'])
    return {'sealed_files':count,'selected_source_files':len(manifest['selected_files']),'prior_Git_blobs':len(old['files'])}
if __name__=='__main__':print(json.dumps(verify(),sort_keys=True))
