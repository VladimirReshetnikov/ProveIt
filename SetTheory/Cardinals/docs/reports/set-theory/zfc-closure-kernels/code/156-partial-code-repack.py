#!/usr/bin/env python3
"""Repack the sealed tree byte-identically using Python/zlib and fixed metadata.
No source files or manifest are changed. Output must be outside the packet.
"""
from pathlib import Path
import argparse,hashlib,json,zipfile
ROOT=Path(__file__).resolve().parent.parent
ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();out=a.output.resolve()
assert not out.is_relative_to(ROOT),'Output must be outside packet'
manifest=json.loads((ROOT/'manifest.json').read_text())['files']
for n,h in manifest.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
names=sorted([*manifest,'manifest.json'])
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9)as z:
 for n in names:
  i=zipfile.ZipInfo(ROOT.name+'/'+n,date_time=(2026,10,20,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,(ROOT/n).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
print(hashlib.sha256(out.read_bytes()).hexdigest(),out)
