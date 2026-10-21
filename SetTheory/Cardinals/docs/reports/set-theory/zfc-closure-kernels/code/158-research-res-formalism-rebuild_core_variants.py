#!/usr/bin/env python3
"""Rebuild six literal core217 alternative tables from the pinned core alone.

The patch data is inherited from the K219 zero-terminal/retagged/composed
alternatives at ProveIt 704b87442afbd571833a628cd558f1d207fd8b2f. The eliminated
301/1 branch has the same old and new action as 88/1, so its duplicate patch is
represented at 88/1. This script checks exact bytes and rows, not runtime.
"""
from pathlib import Path
import argparse,hashlib,json
CORE_SHA='c3d90a672481086329d8ed93da24a885d80a553ae6298b3a6444bea0fd5cee53'
ZERO=[(38,1,(1,'R',53),(1,'R',119)),(53,0,(0,'R',68),(0,'R',108)),(53,1,(1,'R',69),(1,'R',21)),(88,1,(1,'R',103),(1,'R',53)),(103,0,(0,'R',108),(0,'R',228)),(119,0,(0,'R',228),(0,'R',68)),(119,1,(0,'L',103),(1,'R',69)),(134,1,(1,'R',119),(1,'R',103))]
RETAG=[(139,0,(0,'R',160),(0,'R',99)),(139,1,(0,'L',16),(1,'R',160)),(160,1,(1,'R',99),(1,'L',63))]
def load(raw):
 t={};starts=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[2]))
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();key=int(q),int(b);assert key not in t;t[key]=int(w),d,int(z)
 assert starts==[0]
 return t
def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode('ascii')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--core',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();raw=a.core.read_bytes();assert hashlib.sha256(raw).hexdigest()==CORE_SHA;core=load(raw);a.output.mkdir(parents=True,exist_ok=True);records=[]
 for name,patches in [('zero_terminal',ZERO),('retagged',RETAG),('composed',ZERO+[(q,b,old,(0,'L',139)if(q,b)==(139,0)else new)for q,b,old,new in RETAG])]:
  t=core.copy()
  for q,b,old,new in patches:
   assert t[q,b]==old
   t[q,b]=new
  for r157 in[False,True]:
   u=t.copy();tag=name+('-row157'if r157 else'')
   if r157:assert u[157,1]==(1,'L',148);u[157,1]=1,'L',187
   assert len(u)==434 and len({q for q,b in u})==217
   assert {z for w,d,z in u.values()}-{q for q,b in u}=={254}
   result=encode(u);p=a.output/(tag+'.native.tm');p.write_bytes(result);records.append(dict(variant=tag,path=str(p),sha256=hashlib.sha256(result).hexdigest(),working_states=217))
 (a.output/'rebuild.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
if __name__=='__main__':main()
