"""Byte identity checks only; never runs incoming code or the Lean project."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def verify(root=ROOT):
    count=0
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);p=root/name
        if not p.is_file():raise ValueError('missing sealed file: '+name)
        if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:raise ValueError('changed sealed file: '+name)
        count+=1
    src=json.loads((root/'sources/manifest.json').read_text())
    for f in src['selected_files']:
        if hashlib.sha256((root/f['file']).read_bytes()).hexdigest()!=f['sha256']:raise ValueError('source mismatch: '+f['file'])
    a=json.loads((root/'anthropic_snapshot/selected_manifest.json').read_text())
    for f in a['selected_files']:
        b=(root/'anthropic_snapshot'/f['file']).read_bytes()
        h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if h!=f['blob'] or hashlib.sha256(b).hexdigest()!=f['sha256']:raise ValueError('Anthropic source mismatch: '+f['file'])
    return {'sealed_files':count,'selected_proposal_sources':len(src['selected_files']),'selected_Anthropic_source_blobs':len(a['selected_files'])}
if __name__=='__main__':print(json.dumps(verify(),sort_keys=True))
