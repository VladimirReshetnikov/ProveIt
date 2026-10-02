"""Create a deterministic, path-safe source archive and fresh checksum manifest."""
from pathlib import Path, PurePosixPath
import hashlib, sys, zipfile
root = Path(__file__).resolve().parent.parent
out = Path(sys.argv[1]).resolve() if len(sys.argv)>1 else root.parent/'accessible-automata-reproducibility.zip'
allowed_dirs={'code','data','checks'}
allowed_files={'accessible-automata.pdf','accessible-automata.tex','README.md','VERIFICATION.md','SOURCES.md','requirements.txt','build.sh','replay.sh'}
files=[]
for p in root.rglob('*'):
    rel=p.relative_to(root)
    if any(part.startswith('.') or part=='__pycache__' for part in rel.parts):continue
    if p.is_symlink():raise RuntimeError(f'Symlink not allowed: {rel}')
    if not p.is_file():continue
    if len(rel.parts)==1 and rel.name not in allowed_files:continue
    if len(rel.parts)>1 and rel.parts[0] not in allowed_dirs:continue
    if p.suffix in {'.pyc','.zip'}:continue
    files.append(p)
files.sort(key=lambda p:p.relative_to(root).as_posix())
manifest=''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(root).as_posix()}\n' for p in files)
(root/'MANIFEST.sha256').write_text(manifest)
files.append(root/'MANIFEST.sha256')
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in files:
        name='accessible-automata/'+p.relative_to(root).as_posix()
        info=zipfile.ZipInfo(name,(2026,10,2,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=(0o100755 if p.suffix=='.sh' else 0o100644)<<16
        z.writestr(info,p.read_bytes())
with zipfile.ZipFile(out) as z:
    assert z.testzip() is None
    for i in z.infolist():
        p=PurePosixPath(i.filename)
        assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
        assert (i.external_attr>>16)&0o170000 != 0o120000
print(f'Created {out} ({len(files)} files, {out.stat().st_size} bytes)')
print('SHA256',hashlib.sha256(out.read_bytes()).hexdigest())
