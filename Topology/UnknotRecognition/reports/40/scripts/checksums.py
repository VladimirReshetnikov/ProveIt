#!/usr/bin/env python3
"""Write or verify the distributable source/data manifest."""
import argparse,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/'MANIFEST.sha256'
SKIP={'.aux','.log','.out','.toc','.fls','.fdb_latexmk','.pyc'}

def files():
    return sorted(p for p in ROOT.rglob('*') if p.is_file() and p!=MANIFEST
                  and '__pycache__' not in p.parts and p.suffix not in SKIP
                  and not p.name.endswith('.synctex.gz'))

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    if args.write:
        MANIFEST.write_text(''.join(f'{digest(p)}  {p.relative_to(ROOT).as_posix()}\n' for p in files()))
        print(f'Wrote {len(files())} file hashes.');return
    expected={}
    for line in MANIFEST.read_text().splitlines():
        sha,relative=line.split('  ',1)
        p=(ROOT/relative).resolve()
        if ROOT.resolve() not in p.parents:raise ValueError('manifest path escapes package')
        expected[relative]=sha
    actual={p.relative_to(ROOT).as_posix():digest(p) for p in files()}
    if actual!=expected:
        missing=sorted(set(expected)-set(actual));extra=sorted(set(actual)-set(expected))
        changed=sorted(k for k in expected.keys()&actual.keys() if expected[k]!=actual[k])
        raise SystemExit(f'Checksum mismatch: missing={missing}, extra={extra}, changed={changed}')
    print(f'All {len(actual)} file hashes verified.')

if __name__=='__main__':main()
