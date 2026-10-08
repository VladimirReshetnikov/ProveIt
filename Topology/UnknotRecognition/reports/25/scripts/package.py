#!/usr/bin/env python3
"""Build the standalone TeX, SHA-256 manifest, and an integration ZIP.

Compile docs/article.pdf before running. This script does not fetch sources,
modify the upstream repository, or run the optional integration smoke test.
"""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT=Path(__file__).resolve().parents[1]


def included(path):
    rel=path.relative_to(ROOT)
    return (path.is_file() and '__pycache__' not in rel.parts and
            path.suffix not in {'.pyc','.pyo','.aux','.log','.out','.toc','.zip'} and
            path.name != 'SHA256SUMS.txt')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',default=str(ROOT.parent/(ROOT.name+'.zip')))
    args=p.parse_args()
    if not (ROOT/'docs/article.pdf').is_file():
        p.error('compile docs/article.pdf first')
    text=(ROOT/'docs/article.tex').read_text()
    for fragment in ('benchmark_table','default_table','radius_table'):
        text=text.replace(r'\input{'+fragment+'.tex}',(ROOT/'docs'/(fragment+'.tex')).read_text().rstrip())
    (ROOT/'docs/article_standalone.tex').write_text(text)
    files=sorted(path for path in ROOT.rglob('*') if included(path))
    rows=[hashlib.sha256(path.read_bytes()).hexdigest()+'  '+str(path.relative_to(ROOT)) for path in files]
    (ROOT/'SHA256SUMS.txt').write_text('\n'.join(rows)+'\n')
    files.append(ROOT/'SHA256SUMS.txt')
    out=Path(args.output).resolve()
    if out==ROOT or ROOT in out.parents:
        p.error('archive output must be outside the source package')
    with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for path in files:
            z.write(path,str(Path(ROOT.name)/path.relative_to(ROOT)))
    with zipfile.ZipFile(out) as z:
        bad=z.testzip()
        if bad:
            raise RuntimeError('ZIP validation failed: '+bad)
    print(json.dumps(dict(archive=str(out),files=len(files),bytes=out.stat().st_size,
                          sha256=hashlib.sha256(out.read_bytes()).hexdigest()),indent=2))

if __name__=='__main__':
    main()
