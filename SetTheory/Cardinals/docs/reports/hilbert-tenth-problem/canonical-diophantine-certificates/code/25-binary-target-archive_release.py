#!/usr/bin/env python3
"""Create a deterministic stored ZIP after authenticating Report 52."""
import sys
if not sys.flags.isolated or sys.flags.optimize:raise SystemExit('Use python3 -I without -O')
import argparse,hashlib,json,os,stat,subprocess,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def require(ok,why):
    if not ok:raise RuntimeError(why)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--manifest-sha256',required=True);a=ap.parse_args()
    p=a.output.absolute();require('..' not in a.output.parts,'Parent traversal forbidden')
    for q in [p]+list(p.parents):require(not q.is_symlink(),'Output symlink forbidden')
    require(not p.exists() and p.parent.is_dir(),'Output must be new with existing parent');p=p.resolve();require(p!=ROOT and ROOT not in p.parents and p not in ROOT.parents,'Output overlaps release')
    v=subprocess.run([sys.executable,'-I',str(ROOT/'verify_release.py'),'--manifest-sha256',a.manifest_sha256],capture_output=True,text=True,timeout=120);require(v.returncode==0,'Release integrity failed: '+v.stderr)
    entries=[q for q in sorted(ROOT.rglob('*')) if q.is_file()]
    before={q.relative_to(ROOT).as_posix():hashlib.sha256(q.read_bytes()).hexdigest() for q in entries}
    with zipfile.ZipFile(p,'x',compression=zipfile.ZIP_STORED,allowZip64=True) as z:
        for q in entries:
            zi=zipfile.ZipInfo(q.relative_to(ROOT).as_posix(),(2026,10,4,0,0,0));zi.create_system=3;zi.external_attr=(stat.S_IFREG|0o644)<<16;zi.compress_type=zipfile.ZIP_STORED;z.writestr(zi,q.read_bytes())
    require(before=={q.relative_to(ROOT).as_posix():hashlib.sha256(q.read_bytes()).hexdigest() for q in entries},'Source bytes changed')
    with zipfile.ZipFile(p) as z:
        require(z.testzip() is None,'ZIP CRC failed');require(set(z.namelist())==set(before),'ZIP inventory mismatch')
        for n,d in before.items():require(hashlib.sha256(z.read(n)).hexdigest()==d,'ZIP entry differs: '+n)
    print(json.dumps({'schema':'report52-archive-v1','status':'PASS','archive_bytes':p.stat().st_size,'archive_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'entries':len(entries),'sorted_fixed_timestamp_stored_zip':True,'archive_payloads_verified':True},indent=2,sort_keys=True))
if __name__=='__main__':main()
