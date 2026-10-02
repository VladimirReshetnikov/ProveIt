"""Safely extract a ZIP into a new directory. Usage: python safe_extract.py ZIP DEST"""
from pathlib import Path, PurePosixPath
import stat, sys, zipfile
archive=Path(sys.argv[1]); dest=Path(sys.argv[2])
if dest.exists(): raise SystemExit('Destination must not exist')
with zipfile.ZipFile(archive) as z:
    entries=z.infolist(); names=set(); total=0
    for i in entries:
        p=PurePosixPath(i.filename)
        if (p.is_absolute() or '..' in p.parts or not p.parts or '\\' in i.filename
            or ':' in p.parts[0] or i.filename in names):
            raise SystemExit('Unsafe or duplicate ZIP path: '+i.filename)
        mode=(i.external_attr>>16)&0xFFFF
        if stat.S_ISLNK(mode): raise SystemExit('Symlink rejected: '+i.filename)
        if stat.S_IFMT(mode) not in (0,stat.S_IFREG,stat.S_IFDIR):
            raise SystemExit('Nonregular entry rejected: '+i.filename)
        names.add(i.filename); total+=i.file_size
    if total>100_000_000: raise SystemExit('Expanded archive exceeds 100 MB safety limit')
    dest.mkdir(parents=True)
    for i in entries:
        out=dest.joinpath(*PurePosixPath(i.filename).parts)
        if not out.resolve().is_relative_to(dest.resolve()): raise SystemExit('Escape rejected')
        if i.is_dir(): out.mkdir(parents=True,exist_ok=True)
        else:
            out.parent.mkdir(parents=True,exist_ok=True)
            with z.open(i) as src, out.open('xb') as dst:
                while chunk:=src.read(1024*1024): dst.write(chunk)
print('Extracted safely to',dest)
