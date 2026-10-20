#!/usr/bin/env python3
"""Exercise packet-integrity rejection on private temporary copies only."""
from pathlib import Path
import argparse,importlib.util,json,shutil,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('packet_reproduce',ROOT/'portable/reproduce.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not sys.flags.optimize
 results=[]
 with tempfile.TemporaryDirectory(prefix='k218-integrity-controls-')as temp:
  root=Path(temp)/ROOT.name;shutil.copytree(ROOT,root);r.ROOT=root
  r.verify_manifest()
  original=(root/'README.md').read_bytes()
  def reject(name):
   try:r.verify_manifest()
   except(ValueError,AssertionError)as e:results.append(dict(name=name,status='REJECTED',reason=str(e)))
   else:raise AssertionError('Accepted corrupt packet: '+name)
  (root/'README.md').write_bytes(original+b'\nCORRUPTED\n');reject('changed_manifested_bytes');(root/'README.md').write_bytes(original)
  (root/'unlisted.txt').write_text('extra');reject('unmanifested_extra_file');(root/'unlisted.txt').unlink()
  (root/'README.md').unlink();reject('missing_manifested_file');(root/'README.md').write_bytes(original)
  manifest=(root/'manifest.json').read_bytes();bad=json.loads(manifest);bad['files'][0]['path']='../escape';(root/'manifest.json').write_text(json.dumps(bad));reject('escaping_manifest_path');(root/'manifest.json').write_bytes(manifest)
  checksum=(root/'SHA256SUMS').read_bytes();(root/'SHA256SUMS').write_bytes(checksum[:-1]+b'X');reject('corrupt_checksum_index');(root/'SHA256SUMS').write_bytes(checksum)
  r.verify_manifest()
 a.output.write_text(json.dumps(dict(status='ALL_MANIFEST_BOUNDARY_CONTROLS_REJECTED',count=len(results),controls=results),indent=2,sort_keys=True)+'\n')
 print('ALL_MANIFEST_BOUNDARY_CONTROLS_REJECTED',len(results))
if __name__=='__main__':main()
