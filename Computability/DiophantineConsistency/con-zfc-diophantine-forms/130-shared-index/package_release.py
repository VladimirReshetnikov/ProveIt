#!/usr/bin/env python3
"""Create the complete file manifest and a deterministic ZIP of this packet.

Temporary LaTeX products and Python caches are excluded. Mathematical artifacts
are never regenerated here; run verify_all.py before distributing the result.
"""
from pathlib import Path
import argparse, hashlib, json, zipfile

HERE = Path(__file__).resolve().parent
TRANSIENT_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.synctex.gz', '.pyc'}


def included(path):
    rel = path.relative_to(HERE)
    if not path.is_file() or '__pycache__' in rel.parts or path.suffix == '.pyc':
        return False
    if rel.as_posix() == 'MANIFEST.json':
        return False
    if rel.parts[0] == 'report' and (
            path.suffix in TRANSIENT_SUFFIXES or path.name.endswith('.synctex.gz')):
        return False
    return True


def paths():
    return sorted((p for p in HERE.rglob('*') if included(p)),
                  key=lambda p: p.relative_to(HERE).as_posix())


def manifest():
    files = []
    for path in paths():
        data = path.read_bytes()
        files.append({'path':path.relative_to(HERE).as_posix(), 'size':len(data),
                      'sha256':hashlib.sha256(data).hexdigest()})
    obj = {'schema':'conzfc-shared-index-release-v1',
           'source_commit':'f4d8db99e060339f3306a04d507c35bc1d0d68c5',
           'explanation':'Every delivered file except this manifest; build temporaries are not delivered.',
           'files':files}
    (HERE/'MANIFEST.json').write_text(json.dumps(obj,indent=2)+'\n')
    return len(files)


def archive(destination):
    destination = destination.resolve()
    if destination.is_relative_to(HERE):
        raise ValueError('ZIP output must be outside the packet directory')
    destination.parent.mkdir(parents=True,exist_ok=True)
    selected = paths()+[HERE/'MANIFEST.json']
    with zipfile.ZipFile(destination,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for path in sorted(selected):
            rel = Path(HERE.name)/path.relative_to(HERE)
            info = zipfile.ZipInfo(rel.as_posix(),date_time=(2026,10,24,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            z.writestr(info,path.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    print(json.dumps({'archive':str(destination),'bytes':destination.stat().st_size,
                      'sha256':hashlib.sha256(destination.read_bytes()).hexdigest()},indent=2))


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--manifest-only',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    count=manifest()
    print('Manifest files:',count)
    if not args.manifest_only:
        archive(args.output or HERE.with_suffix('.zip'))
