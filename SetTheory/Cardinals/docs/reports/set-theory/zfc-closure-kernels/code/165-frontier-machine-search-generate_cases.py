#!/usr/bin/env python3
"""Generate the finite rejection-suite data. These are not universal proofs."""
from pathlib import Path
import argparse,importlib.util,json
HERE=Path(__file__).resolve().parent
def main():
 p=argparse.ArgumentParser();p.add_argument('sites',type=Path);p.add_argument('out',type=Path)
 p.add_argument('--baseline',type=Path,default=HERE.parent/'baseline/k215');a=p.parse_args()
 module=a.baseline/'code/runtime-inputs/runtime/independent_runtime.py'
 s=importlib.util.spec_from_file_location('ir',module);ir=importlib.util.module_from_spec(s);s.loader.exec_module(ir)
 rows=[]
 def cells(v):return ','.join(map(str,sorted(v))) if v else 'x'
 for i,site in enumerate(json.loads(a.sites.read_text())):
  for pos in ([0,1] if site[1]=='CD' else [0]):
   regs=[0]*9
   if pos:regs[site[2]]=1
   initial=ir.frame(site[0],regs,[0],0);expected=ir.expected(site,regs,[0],0)
   halt=int(expected is None);head=0 if halt else expected[0][1];want=set() if halt else expected[0][2]
   rows.append(f'{i} {pos} {halt} {head} {cells(initial)} {cells(want)}')
 a.out.write_text('\n'.join(rows)+'\n');print(len(rows),'cases')
if __name__=='__main__':main()
