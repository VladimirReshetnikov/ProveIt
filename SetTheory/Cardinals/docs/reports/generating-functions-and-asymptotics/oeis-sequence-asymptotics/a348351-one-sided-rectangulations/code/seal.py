#!/usr/bin/env python3
"""Create a deterministic local archive of exactly the manifested files."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def main():
    cp=subprocess.run([sys.executable,'integrity.py'],cwd=ROOT)
    require(cp.returncode==0,'integrity must pass before sealing')
    manifest=json.loads((ROOT/'manifest.json').read_text())
    names=sorted(manifest['files'])+['manifest.json']
    archive=ROOT/'report111_source_checks.zip'
    with ZipFile(archive,'w',compression=ZIP_DEFLATED,compresslevel=9) as z:
        for name in sorted(names):
            info=ZipInfo('report111/'+name,date_time=(2026,10,2,0,0,0))
            info.compress_type=ZIP_DEFLATED
            info.create_system=3
            info.external_attr=0o100644<<16
            z.writestr(info,(ROOT/name).read_bytes(),compress_type=ZIP_DEFLATED,compresslevel=9)
    hashes=''.join(sha256((ROOT/name).read_bytes()).hexdigest()+'  '+name+'\n'
                   for name in ('report111.tex','report111.pdf','report111_source_checks.zip','manifest.json'))
    (ROOT/'FINAL_SHA256.txt').write_text(hashes)
    print(hashes,end='')

if __name__=='__main__':
    main()
