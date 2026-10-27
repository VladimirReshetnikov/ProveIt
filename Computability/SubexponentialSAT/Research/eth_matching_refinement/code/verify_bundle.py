"""Check sealed files; ignores generated unlisted build products."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parent.parent

def verify(root=ROOT):
    count=0
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        p=root/name
        if not p.is_file():raise ValueError('missing sealed file: '+name)
        if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
            raise ValueError('changed sealed file: '+name)
        count+=1
    m=json.loads((root/'sources/manifest.json').read_text())
    for row in m['files']:
        b=(root/'sources'/row['file']).read_bytes()
        if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=row['blob']:
            raise ValueError('source blob mismatch: '+row['file'])
    return dict(sealed_files=count,source_blobs=len(m['files']))

if __name__=='__main__':print(json.dumps(verify(),sort_keys=True))
