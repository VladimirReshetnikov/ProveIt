"""Check the release hashes before running programs that refresh result records."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SHA256.json').read_text())
for name,expected in manifest.items():
    actual=hashlib.sha256((root/name).read_bytes()).hexdigest()
    if actual!=expected:raise RuntimeError(('File differs from release',name,expected,actual))
print('Release integrity verified:',len(manifest),'files')
