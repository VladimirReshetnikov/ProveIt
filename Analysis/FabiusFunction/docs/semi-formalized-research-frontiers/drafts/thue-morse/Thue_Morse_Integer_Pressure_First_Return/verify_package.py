"""Verify the package SHA-256 manifest with the Python standard library."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'PROVENANCE.json').read_text())
for name,want in manifest['files'].items():
    got=hashlib.sha256((root/name).read_bytes()).hexdigest()
    if got!=want:raise ArithmeticError('SHA-256 mismatch: '+name)
print('All '+str(len(manifest['files']))+' recorded SHA-256 values match')
