#!/usr/bin/env python3
"""Deterministic ZIP of a sealed Report46 directory; no research execution."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
output=args.output.resolve()
if output.exists() or ROOT in output.parents:
    raise RuntimeError('Choose a new ZIP path outside the release directory.')
pins=json.loads((ROOT/'MANIFEST.json').read_text())['sha256']
files=[p for p in sorted(ROOT.rglob('*')) if p.is_file()]
actual={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in files if p!=ROOT/'MANIFEST.json'}
if actual!=pins:
    raise RuntimeError('Release manifest mismatch before archive.')
with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in files:
        info=zipfile.ZipInfo('Research_Report46/'+str(p.relative_to(ROOT)),(2026,10,4,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=0o100644<<16
        z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(output) as z:
    if z.testzip() is not None:
        raise RuntimeError('ZIP CRC failure.')
print(json.dumps({'status':'PASS','bytes':output.stat().st_size,'files':len(files),
                  'sha256':hashlib.sha256(output.read_bytes()).hexdigest()},sort_keys=True))
