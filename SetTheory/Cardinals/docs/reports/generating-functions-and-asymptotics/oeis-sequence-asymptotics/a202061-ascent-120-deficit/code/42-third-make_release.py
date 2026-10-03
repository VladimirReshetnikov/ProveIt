#!/usr/bin/env python3
"""Build an exact deterministic release only after hash-bound integrated review."""
from pathlib import Path
import hashlib,zipfile,subprocess
root=Path(__file__).resolve().parent
sources=['a202061-third-order.tex','proofs/upper-section.tex','proofs/lower-section.tex','proofs/inverse-section.tex','a202061-third-order.pdf']
review=root/'audit/integrated-report-review.md'
assert review.is_file(),'Integrated review is required before release'
review_text=review.read_text()
for name in sources:
    digest=hashlib.sha256((root/name).read_bytes()).hexdigest()
    assert digest in review_text,f'Missing current hash-bound integrated signoff: {name}'
for line in (root/'audit/audited-proof-sha256.txt').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,f'Changed audited proof: {name}'
subprocess.run(['python',str(root/'checks/check_dependencies.py')],check=True)
subprocess.run(['python',str(root/'checks/check_proof_sources.py')],check=True)
def include(p):
    r=p.relative_to(root)
    return p.is_file() and r.as_posix()!='SHA256SUMS' and not any(a.startswith('.') or a=='__pycache__' for a in r.parts) and p.suffix!='.pyc'
files=sorted((p for p in root.rglob('*') if include(p)),key=lambda p:p.relative_to(root).as_posix())
(root/'SHA256SUMS').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root).as_posix()}\n' for p in files))
files.append(root/'SHA256SUMS')
archive=root.parent/(root.name+'.zip')
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(files):
        info=zipfile.ZipInfo(root.name+'/'+p.relative_to(root).as_posix(),date_time=(2026,10,2,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=(p.stat().st_mode&0xffff)<<16
        z.writestr(info,p.read_bytes())
digest=hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix(archive.suffix+'.sha256').write_text(f'{digest}  {archive.name}\n')
print(f'{archive}: {archive.stat().st_size} bytes; {len(files)-1} manifested payload files')
print(digest)
