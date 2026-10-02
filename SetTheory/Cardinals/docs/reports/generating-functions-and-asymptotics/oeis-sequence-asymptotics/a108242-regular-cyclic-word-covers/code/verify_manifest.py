"""Verify all release hashes without external commands."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
count=0
for line in (root/'MANIFEST.sha256').read_text().splitlines():
    digest,name=line.split('  ',1);p=root/name
    assert p.resolve().is_relative_to(root),name
    assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
    count+=1
print('PASS:',count,'release file hashes')
