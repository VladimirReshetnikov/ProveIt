#!/usr/bin/env python3
"""Relocated end-to-end replay; all receipt writes remain in the fresh copy."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']
 with tempfile.TemporaryDirectory(prefix='positive23_relocated_') as temp:
  dst=Path(temp)/'artifact';shutil.copytree(ROOT,dst,ignore=shutil.ignore_patterns('__pycache__'))
  for r,h in pins.items():
   if sha(dst/r)!=h:raise ValueError('relocated source pin '+r)
  cp=subprocess.run(['sh',str(dst/'reproduce.sh')],cwd=temp,check=True,capture_output=True,text=True)
  for r,h in pins.items():
   if sha(dst/r)!=h:raise ValueError('replay changed pinned file '+r)
  if (dst/'CHECK.json').read_bytes()!=(ROOT/'CHECK.json').read_bytes():raise ValueError('location-sensitive receipt')
  rec={'status':'PASS','all_source_pins_unchanged':len(pins),'normal_optimized_receipts_equal':True,'relocated_receipt_matches_original':True,'isolated_copy':True,'commands':'reproduce.sh: new graph rebuild; both full new deep/mutation modes; parent rebuild and both deep/mutation modes; exact parent receipt comparison','output_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest(),'stderr':cp.stderr}
  if a.receipt:a.receipt.write_text(json.dumps(rec,indent=2)+'\n')
  print(json.dumps(rec,indent=2))
if __name__=='__main__':main()
