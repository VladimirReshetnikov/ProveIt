#!/usr/bin/env python3
"""Portable full exact proof replay. Standard library only."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def integrity():
 count=0
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,name=line.split('  ',1)
  path=ROOT/name
  if not path.is_file():raise RuntimeError('Missing file: '+name)
  actual=hashlib.sha256(path.read_bytes()).hexdigest()
  if actual!=digest:raise RuntimeError('Hash mismatch: '+name)
  count+=1
 return count

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['full','hashes'],default='full');ap.add_argument('--output');ap.add_argument('--workers',type=int,default=4);a=ap.parse_args()
 if a.workers<1:ap.error('--workers must be positive')
 start=time.time();count=integrity();result={'pass':True,'mode':a.mode,'integrity_entries':count}
 if a.mode=='full':
  with tempfile.TemporaryDirectory(prefix='five-core-proof-')as temp:
   temp=Path(temp);src=temp/'certificate-data';shutil.copytree(ROOT/'certificate-data',src)
   checker=temp/'check.py';shutil.copyfile(ROOT/'proof-check/check.py',checker)
   output=temp/'fresh-certificate-receipt.json'
   subprocess.run([sys.executable,str(checker),str(src),str(output),str(a.workers)],check=True)
   result['certificate_replay']=json.loads(output.read_text())
   example=temp/'check_strengthening_counterexample.py';shutil.copyfile(ROOT/'proof-check/check_strengthening_counterexample.py',example)
   subprocess.run([sys.executable,str(example)],check=True)
   result['counterexample_replay']=json.loads((temp/'strengthening-counterexample-receipt.json').read_text())
 result['elapsed_seconds']=round(time.time()-start,3)
 if a.output:Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
