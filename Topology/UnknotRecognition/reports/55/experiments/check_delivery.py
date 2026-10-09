"""Check the shipped manifest and the source binding of recorded experiments."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
manifest=json.loads((ROOT/'SHA256SUMS.json').read_text())
for name,expected in manifest.items():
    path=ROOT/name
    if not path.is_file():raise SystemExit('Missing artifact: '+name)
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual!=expected:raise SystemExit('Artifact changed: '+name)
for name in ('audit.json','benchmark.json'):
    result=json.loads((ROOT/'results'/name).read_text())
    for rel,expected in result['source_sha256'].items():
        actual=hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()
        if actual!=expected:raise SystemExit(name+' uses a different source: '+rel)
print('PASS:',len(manifest),'artifact hashes and both experiment source bindings')
