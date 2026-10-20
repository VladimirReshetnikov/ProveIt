#!/usr/bin/env python3
"""Regenerate the deliverable inventory after an intentional packet change.

Excluded files are LaTeX build intermediates, Python caches, and the two
inventory files themselves. Validation is in reproduce.py. Regeneration
records bytes; it does not perform any mathematical verification.
"""
from pathlib import Path
import argparse, hashlib, json

SKIP_SUFFIXES = {'.aux', '.log', '.toc', '.out', '.fls', '.fdb_latexmk', '.synctex.gz', '.pyc'}
def members(root):
    for p in sorted(root.rglob('*')):
        if not p.is_file():
            continue
        rel = p.relative_to(root)
        if p.is_symlink():
            raise ValueError('Symlink is not a deliverable member: '+str(rel))
        if '__pycache__' in rel.parts or p.name in ('MANIFEST.json', 'SHA256SUMS'):
            continue
        # Preserve verification/ and vendor/ logs; only report build files are transient.
        if rel.parts[0] == 'report' and (p.suffix in SKIP_SUFFIXES or p.name.endswith('.synctex.gz')):
            continue
        if p.suffix == '.pyc':
            continue
        yield p, rel.as_posix()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    a = ap.parse_args(); root = a.root.resolve()
    files = [dict(path=name, size=p.stat().st_size,
                  sha256=hashlib.sha256(p.read_bytes()).hexdigest())
             for p,name in members(root)]
    data = dict(format='K222-research-artifact-manifest-v1',
                baseline_commit='076445a2664854d817f8a938731dcacc290dcd7b',
                excluded='MANIFEST.json, SHA256SUMS, Python caches, report build intermediates',
                files=files)
    manifest = root/'MANIFEST.json'
    manifest.write_text(json.dumps(data, indent=2)+'\n')
    sums = ''.join(f"{x['sha256']}  {x['path']}\n" for x in files)
    sums += hashlib.sha256(manifest.read_bytes()).hexdigest()+'  MANIFEST.json\n'
    (root/'SHA256SUMS').write_text(sums)
    print(json.dumps(dict(status='MANIFEST_GENERATED', files=len(files),
                         bytes=sum(x['size'] for x in files))))

if __name__ == '__main__':
    main()
