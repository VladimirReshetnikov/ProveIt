#!/usr/bin/env python3
"""Create a deterministic release only after current integrated review."""
from pathlib import Path
import hashlib, zipfile, subprocess
root=Path(__file__).resolve().parent
sources=['a202061-allorders.tex','proofs/reduction-section.tex','proofs/action-section.tex','proofs/inverse-section.tex','proofs/checks-scope-section.tex','a202061-allorders.pdf']
review=root/'audit/integrated-report-review.md'
assert review.is_file(),'Integrated review required'
text=review.read_text()
for name in sources:
 h=hashlib.sha256((root/name).read_bytes()).hexdigest()
 assert h in text,f'Missing current hash-bound signoff: {name}'
qa=(root/'audit/visual-qa.md').read_text()
assert hashlib.sha256((root/'a202061-allorders.pdf').read_bytes()).hexdigest() in qa,'Current all-page visual review required'
subprocess.run(['python',str(root/'checks/check_dependencies.py')],check=True)
subprocess.run(['python',str(root/'checks/check_proof_sources.py')],check=True)
def included(p):
 rel=p.relative_to(root)
 return p.is_file() and rel.as_posix()!='SHA256SUMS' and not any(a.startswith('.') or a=='__pycache__' for a in rel.parts) and p.suffix!='.pyc'
files=sorted((p for p in root.rglob('*') if included(p)),key=lambda p:p.relative_to(root).as_posix())
(root/'SHA256SUMS').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root).as_posix()}\n' for p in files))
files.append(root/'SHA256SUMS')
archive=root.parent/(root.name+'.zip')
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files,key=lambda p:p.relative_to(root).as_posix()):
  info=zipfile.ZipInfo(root.name+'/'+p.relative_to(root).as_posix(),date_time=(2026,10,2,0,0,0))
  info.compress_type=zipfile.ZIP_DEFLATED
  info.create_system=3
  info.external_attr=(0o100755 if p.suffix=='.sh' else 0o100644)<<16
  z.writestr(info,p.read_bytes())
h=hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix('.zip.sha256').write_text(f'{h}  {archive.name}\n')
print(f'{archive.name}: {archive.stat().st_size} bytes; {len(files)-1} manifested payload files')
print(h)
