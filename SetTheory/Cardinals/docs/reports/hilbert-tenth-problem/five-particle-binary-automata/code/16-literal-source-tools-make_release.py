#!/usr/bin/env python3
"""Create a deterministic portable ZIP from the exact Report 16 inventory."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,zipfile
ROOT=Path(__file__).resolve().parents[1]
def require(ok,message):
    if not ok:raise RuntimeError(message)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);a=p.parse_args()
    require(not a.output.resolve().is_relative_to(ROOT),'ZIP must be outside the package')
    subprocess.run([sys.executable,str(ROOT/'tools/make_manifest.py')],check=True)
    m=json.loads((ROOT/'manifest.json').read_text())
    paths=sorted([*m['files'],'manifest.json','SHA256SUMS'])
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(a.output,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for rel in paths:
            f=ROOT/rel;require(f.is_file() and not f.is_symlink(),'Expected regular file: '+rel)
            info=zipfile.ZipInfo(ROOT.name+'/'+rel,date_time=(2026,10,3,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
            z.writestr(info,f.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    require(a.output.stat().st_size<=32*1024*1024,'ZIP exceeds 32 MiB upload ceiling')
    print(json.dumps({'archive':str(a.output),'bytes':a.output.stat().st_size,'sha256':hashlib.sha256(a.output.read_bytes()).hexdigest(),'files':len(paths),'manifest_sha256':hashlib.sha256((ROOT/'manifest.json').read_bytes()).hexdigest()},indent=2))
if __name__=='__main__':main()
