"""Verify the immutable files supplied with the archive before a replay."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
n=0
for line in (root/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split('  ',1)
 p=root/name
 assert p.is_file(),f'Missing: {name}'
 assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'Hash mismatch: {name}'
 n+=1
print(f'PASS: {n} package file SHA-256 values verified')
