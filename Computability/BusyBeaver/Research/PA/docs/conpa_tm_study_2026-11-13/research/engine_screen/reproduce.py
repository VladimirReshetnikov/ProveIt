#!/usr/bin/env python3
"""Replay the bounded deletion screens against the exact admitted contexts.
This does not recollect or prove the context overapproximation. Its provenance
and independent unary/list checker are described in README.txt and receipts.
Requires g++ with C++17 support; no external Python package is needed.
"""
from pathlib import Path
import hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(x,m):
 if not x:raise ValueError(m)
def main():
 table=ROOT/'machines/h_only_mp_h.tm';ctx=HERE/'source_contexts.txt'
 require(sha(table)=='bd74754d75e7b8ba97fa7bfc104374de33ae603fc183ae7f08f053ab8c9ea592','machine bytes')
 require(sha(ctx)=='08db7b75790e8330ca8374f23c13a0c5ab920e379623f51883451532074a7fba','context bytes')
 records=[]
 for name in ['scan_helper','scan_two_rows','two_arbitrary_rows']:
  binary=HERE/(name+'.bin')
  subprocess.run(['g++','-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(binary)],check=True)
  start=time.monotonic()
  result=subprocess.run([str(binary),str(table),str(ctx),str(HERE/('reproduced_'+name+'_results.txt')),'196'],text=True,capture_output=True,check=True)
  require('survivors 0' in result.stdout,'no-survivor result changed')
  records.append(dict(name=name,stdout=result.stdout,stderr=result.stderr,seconds=time.monotonic()-start))
  print(name,result.stdout.strip(),flush=True)
 (HERE/'reproduced_screen_receipt.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':main()
