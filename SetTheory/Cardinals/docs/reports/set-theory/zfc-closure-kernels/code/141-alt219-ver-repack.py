#!/usr/bin/env python3
"""Deterministic ZIP of a fully sealed packet. Does not modify packet files."""
from pathlib import Path
import argparse,hashlib,stat,sys,zipfile

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=a.output.resolve()
 assert root.is_dir() and root not in out.parents and not out.exists()
 files=sorted(p for p in root.rglob('*')if p.is_file());assert files
 with zipfile.ZipFile(out,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9)as z:
  for p in files:
   assert not p.is_symlink();name=root.name+'/'+p.relative_to(root).as_posix()
   info=zipfile.ZipInfo(name,date_time=(2026,10,20,0,0,0));info.create_system=3;info.external_attr=(stat.S_IFREG|0o644)<<16;info.compress_type=zipfile.ZIP_DEFLATED
   z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
 print(hashlib.sha256(out.read_bytes()).hexdigest(),out.name)
if __name__=='__main__':main()
