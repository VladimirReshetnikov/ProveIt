#!/usr/bin/env python3
"""Exact old/new blank-start checkpoint comparison; finite startup only."""
import argparse,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE/'vendor'))
import independent_runtime as ir

def step(T,q,h,ones):
 w,d,z=T[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 return z,h+d

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,default=HERE/'input3.tm');ap.add_argument('--new',type=Path,default=HERE/'ft-frontier/machine.native.tm');ap.add_argument('--output',type=Path,default=HERE/'ft-frontier/startup-rows.json');a=ap.parse_args()
 T=ir.table(a.old);q=h=0;ones=set()
 for _ in range(70506):q,h=step(T,q,h,ones)
 want=q,h,ones.copy();assert q==84
 T=ir.table(a.new);q=h=0;ones=set();rows=set();first=None
 for tick in range(100000):
  if(q,h,ones)==want:break
  if q==84 and first is None:first=tick
  rows.add((q,int(h in ones)));q,h=step(T,q,h,ones)
 else:raise AssertionError('Startup join not found')
 r={'old_steps':70506,'new_steps':tick,'first_dispatch':first,'q':q,'h':h,'ones':sorted(ones),'rows':sorted(rows),'status':'EXACT_BLANK_STARTUP_JOIN'};a.output.write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k not in('rows','ones')})
if __name__=='__main__':main()
