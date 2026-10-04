#!/usr/bin/env python3
"""Deterministic authenticated ZIP, fresh output external to release."""
import argparse,hashlib,pathlib,sys,zipfile
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from verify_release import ROOT,authenticate,external_new,snapshot,need

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--output',required=True,type=pathlib.Path);a=p.parse_args()
 authenticate(a.manifest_sha256);before=snapshot(ROOT);out=external_new(a.output)
 with out.open('xb') as stream:
  with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
   for f in sorted(ROOT.rglob('*')):
    if not f.is_file():continue
    info=zipfile.ZipInfo('Research_Report47/'+f.relative_to(ROOT).as_posix(),(2026,10,4,0,0,0));info.create_system=3;info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
    z.writestr(info,f.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
 need(snapshot(ROOT)==before,'Release changed during archive build')
 print('SHA256 '+hashlib.sha256(out.read_bytes()).hexdigest()+'  '+out.name)
if __name__=='__main__':main()
