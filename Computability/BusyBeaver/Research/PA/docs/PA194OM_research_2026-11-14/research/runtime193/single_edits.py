#!/usr/bin/env python3
"""Canonical enumeration used by the single-row bootstrap screen."""
from pathlib import Path
HERE=Path(__file__).resolve().parent

def table():
 out={}
 for line in(HERE/'runtime193.native.tm').read_text().splitlines():
  q,b,w,d,n=line.split();out[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
 return out

def edits():
 T=table();states=sorted({q for q,b in T});i=0
 for(q,b),old in sorted(T.items()):
  for w in(0,1):
   for d in(-1,1):
    for n in states:
     if(w,d,n)==old:continue
     i+=1;yield i,(q,b),(w,d,n)
 assert i==297607

def lookup(ids):
 wanted=set(ids);return {i:(key,act)for i,key,act in edits()if i in wanted}

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args()
 with a.output.open('w')as f:
  for i,(q,b),(w,d,n)in edits():f.write(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n')
 print('Wrote297607 nonterminal-target rewrites')
