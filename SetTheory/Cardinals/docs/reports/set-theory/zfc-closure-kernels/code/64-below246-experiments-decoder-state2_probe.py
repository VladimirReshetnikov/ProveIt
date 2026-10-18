#!/usr/bin/env python3
import sys,json,os
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC246_BASE',ROOT.parents[1]/'baseline/context246'))
sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import read_table,program_sites,paint,expected,PHYSICAL
T=read_table(BASE/'machine/zfc_prefix246_old.tm')
S=program_sites(BASE/'sources/Prog254.v')
records=[];census=Counter();tested=0;worst={}
for p,op,r in S:
 for pos in ([False,True] if op=='CD' else [None]):
  regs=[0]*9
  if op=='CD':regs[PHYSICAL[r]]=int(pos)
  want=expected(p,op,r,regs,[0],0,71)
  one=paint(p,71,regs,[0],0);q=96;h=0;old=None
  for k in range(4000):
   b=int(h in one)
   if q==2 and (old is None or old[0]!=2):
    z=0
    while h-z not in one:z+=1
    last=-1
    if old is not None:last=(old[0],old[1])
    census[last,z]+=1
    if z>8:records.append(dict(pc=p,op=op,r=r,positive=pos,step=k,head=h,zero_run=z,origin=last,ones=sorted(one)))
    if last not in worst or worst[last]['zero_run']<z:worst[last]=dict(pc=p,op=op,r=r,positive=pos,step=k,head=h,zero_run=z,origin=last,ones=sorted(one))
   old=(q,b)
   w,d,q=T[q,b]
   if w:one.add(h)
   else:one.discard(h)
   h+=d
   if q==254:
    assert op=='CH';break
   if q==96 and want is not None and h==want[0] and one==want[1]:break
  else:raise AssertionError((p,op,r,'fuel'))
  tested+=1
print('tested',tested,'zero_run_longer8',len(records))
print('census',sorted(census.items()))
for k,v in worst.items():print('worst',k,v)
Path(__file__).with_name('state2-contexts.json').write_text(json.dumps(dict(tested=tested,census=[dict(source=list(k[0])if isinstance(k[0],tuple) else k[0],zero_run=k[1],events=v)for k,v in census.items()],bad=records,worst=list(worst.values())),indent=2))
