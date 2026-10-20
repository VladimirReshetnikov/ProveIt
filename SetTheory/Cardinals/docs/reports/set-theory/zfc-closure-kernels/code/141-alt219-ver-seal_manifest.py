#!/usr/bin/env python3
"""Regenerate exact manifest and checksum inventory before deterministic sealing."""
from pathlib import Path
import argparse,hashlib,json

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);a=ap.parse_args();root=a.root.resolve()
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 files=[]
 for p in sorted(root.rglob('*')):
  assert not p.is_symlink() and '__pycache__'not in p.parts
  if p.is_file()and p not in(root/'manifest.json',root/'SHA256SUMS'):
   files.append(dict(path=p.relative_to(root).as_posix(),size=p.stat().st_size,sha256=sha(p)))
 (root/'manifest.json').write_text(json.dumps(dict(schema_version=1,files=files),indent=2,sort_keys=True)+'\n')
 names=sorted([x['path']for x in files]+['manifest.json'])
 (root/'SHA256SUMS').write_text(''.join(f'{sha(root/n)}  {n}\n'for n in names))
 print(len(files),'manifest entries')
if __name__=='__main__':main()
