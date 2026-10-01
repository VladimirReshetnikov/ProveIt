"""Verify every recorded package SHA-256; Python standard library only."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'PROVENANCE.json').read_text())
# ed. (2026-10-01): the three inputs/ copies were not filed in ProveIt (they are
# ../Thue_Morse_Integer_Pressure_First_Negative/ and its source archive); an absent
# file is reported and skipped, and every filed file is still checked.
skipped=[]
for name,want in manifest['files'].items():
    if not (root/name).exists():  # ed. (2026-10-01): an unfiled copy
        skipped.append(name);continue
    got=hashlib.sha256((root/name).read_bytes()).hexdigest()
    if got != want: raise ArithmeticError('SHA-256 mismatch: '+name)
print('All '+str(len(manifest['files'])-len(skipped))+' recorded SHA-256 values of filed files match')  # ed. (2026-10-01)
if skipped:print('Not filed, not checked: '+', '.join(skipped))  # ed. (2026-10-01)
