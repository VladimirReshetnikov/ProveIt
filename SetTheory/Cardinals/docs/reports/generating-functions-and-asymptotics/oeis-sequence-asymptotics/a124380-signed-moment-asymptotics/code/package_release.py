#!/usr/bin/env python3
"""Build a source-and-results archive, excluding transient TeX/QA caches."""
from pathlib import Path
import hashlib, zipfile
root=Path(__file__).resolve().parent
paths=[root/'a124380-asymptotics.pdf',root/'a124380-asymptotics.tex',root/'README.md',root/'requirements.txt',root/'build.sh',root/'package_release.py']
paths+=sorted((root/'code').glob('*.py'))
paths+=sorted((root/'receipts').glob('*.json'))
paths+=[root/'receipts'/n for n in ['verification.log','independent-checks.log','oscillatory-elementary.log','oscillatory-saddle.log','visual-qa.txt']]
assert all(p.is_file() for p in paths)
manifest=root/'SHA256SUMS'
manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))+'\n' for p in sorted(paths)))
paths.append(manifest)
out=root/'a124380-reproducibility.zip'
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(paths):z.write(p,'a124380-asymptotics/'+str(p.relative_to(root)))
print(out)
print('SHA256',hashlib.sha256(out.read_bytes()).hexdigest())
print('BYTES',out.stat().st_size,'FILES',len(paths))
