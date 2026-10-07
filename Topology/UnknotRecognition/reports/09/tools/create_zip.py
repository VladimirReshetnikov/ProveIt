#!/usr/bin/env python3
"""Build the research handoff ZIP and a deterministic content-hash manifest.

Excludes bytecode, LaTeX auxiliary/log files, and editor files.  Generated
PDFs, tables, figures, bibliography output, raw data, and source snapshots
are retained.  ZIP entries use a fixed research-date timestamp.
"""
from __future__ import annotations
import argparse
import hashlib
from io import BytesIO
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[1]
EXCLUDED_SUFFIXES={'.pyc','.pyo','.aux','.log','.out','.toc','.fls','.fdb_latexmk','.blg'}


def included(path):
    rel=path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in rel.parts
            and not any(part.startswith('.') for part in rel.parts)
            and path.suffix not in EXCLUDED_SUFFIXES
            and not path.name.endswith(('.synctex.gz','~'))
            and path.name!='SHA256SUMS')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT.parent/(ROOT.name+'.zip'))
    args=parser.parse_args()
    paths=sorted((p for p in ROOT.rglob('*') if included(p)),
                 key=lambda p:p.relative_to(ROOT).as_posix())
    manifest=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+
                     p.relative_to(ROOT).as_posix()+'\n' for p in paths)
    (ROOT/'SHA256SUMS').write_text(manifest)
    paths.append(ROOT/'SHA256SUMS')
    buffer=BytesIO()
    with zipfile.ZipFile(buffer,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for p in sorted(paths,key=lambda p:p.relative_to(ROOT).as_posix()):
            info=zipfile.ZipInfo(ROOT.name+'/'+p.relative_to(ROOT).as_posix(),date_time=(2026,10,7,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=(0o100755 if p.suffix=='.sh' else 0o100644)<<16
            archive.writestr(info,p.read_bytes())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_bytes(buffer.getvalue())
    with zipfile.ZipFile(args.output) as archive:
        assert archive.testzip() is None
        names=set(archive.namelist())
        for line in manifest.splitlines():
            digest,name=line.split('  ',1)
            assert hashlib.sha256(archive.read(ROOT.name+'/'+name)).hexdigest()==digest,name
        assert ROOT.name+'/article/unknot_progress.pdf' in names
        assert ROOT.name+'/article/article.tex' in names
    print(f'Created {args.output.name}: {len(paths)} files, {args.output.stat().st_size} bytes.')
    print('SHA256 '+hashlib.sha256(args.output.read_bytes()).hexdigest())


if __name__=='__main__':main()
