#!/usr/bin/env python3
"""Create a deterministic authenticated ZIP outside this release, never overwrite."""
import argparse, hashlib, pathlib, sys, zipfile
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from verify_release import ROOT,authenticate,external_new,snapshot,need

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--output',required=True,type=pathlib.Path);a=p.parse_args()
 authenticate(a.manifest_sha256);before=snapshot(ROOT);out=external_new(a.output)
 with out.open('xb') as stream:
  with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
   for f in sorted(ROOT.rglob('*')):
    if not f.is_file():continue
    name='ant-initialization-report42/'+f.relative_to(ROOT).as_posix();i=zipfile.ZipInfo(name,(2026,10,3,0,0,0));i.create_system=3;i.external_attr=(0o100644<<16);i.compress_type=zipfile.ZIP_DEFLATED
    z.writestr(i,f.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
 need(snapshot(ROOT)==before,'Release changed during archive build')
 print('SHA256 '+hashlib.sha256(out.read_bytes()).hexdigest()+'  '+out.name)
if __name__=='__main__':main()
