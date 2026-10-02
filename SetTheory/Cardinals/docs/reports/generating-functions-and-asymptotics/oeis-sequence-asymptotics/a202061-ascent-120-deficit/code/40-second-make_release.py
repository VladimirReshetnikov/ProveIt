#!/usr/bin/env python3
"""Create a deterministic, manifest-bound ZIP after integrated review."""
from pathlib import Path
import hashlib
import zipfile
import subprocess
root=Path(__file__).resolve().parent
sources=['a202061-second-order.tex','proofs/lower-section.tex',
         'proofs/upper-section.tex','proofs/corollaries-section.tex',
         'proofs/finite-height-section.tex','proofs/conjectural-outlook.tex']
review=root/'audit/integrated-report-review.md'
assert review.is_file(),'Integrated article audit is required before release'
review_text=review.read_text()
for name in sources:
    digest=hashlib.sha256((root/name).read_bytes()).hexdigest()
    assert digest in review_text,f'Current source needs hash-bound integrated signoff: {name}'
for line in (root/'audit/audited-source-sha256.txt').read_text().splitlines():
    digest,original=line.split('  ',1)
    p=root/'proofs'/Path(original).name
    assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'Changed reviewed proof note: {p.name}'
subprocess.run(['python',str(root/'checks/check_dependencies.py')],check=True)

def include(p):
    rel=p.relative_to(root)
    return p.is_file() and rel.as_posix()!='SHA256SUMS' and not any(
        part.startswith('.') or part=='__pycache__' for part in rel.parts
    ) and p.suffix!='.pyc'
files=sorted((p for p in root.rglob('*') if include(p)),key=lambda p:p.relative_to(root).as_posix())
manifest=''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root).as_posix()}\n' for p in files)
(root/'SHA256SUMS').write_text(manifest)
files.append(root/'SHA256SUMS')
archive=root.parent/(root.name+'.zip')
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(files):
        info=zipfile.ZipInfo(root.name+'/'+p.relative_to(root).as_posix(),date_time=(2026,10,2,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=(p.stat().st_mode & 0xffff)<<16
        z.writestr(info,p.read_bytes())
digest=hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix(archive.suffix+'.sha256').write_text(f'{digest}  {archive.name}\n')
print(f'{archive}: {archive.stat().st_size} bytes; {len(files)-1} manifested payload files')
print(digest)
