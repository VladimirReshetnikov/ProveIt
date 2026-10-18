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
records=[];counter=Counter();tested=0
for p,op,r in S:
 for pos in ([False,True] if op=='CD' else [None]):
  regs=[0]*9
  if op=='CD':regs[PHYSICAL[r]]=int(pos)
  want=expected(p,op,r,regs,[0],0,40)
  one=paint(p,40,regs,[0],0);q=96;h=0;history=[];found=[]
  for k in range(3000):
   b=int(h in one)
   if q==74 and b==1:
    rec=dict(pc=p,op=op,r=r,positive=pos,step=k,head=h,ones=sorted(one),previous=history[-18:])
    records.append(rec);counter[(op,r,pos)]+=1
   history.append((q,h,b))
   w,d,q=T[q,b]
   if w:one.add(h)
   else:one.discard(h)
   h+=d
   if q==254:
    assert op=='CH';break
   if q==96 and want is not None and h==want[0] and one==want[1]:break
  else:raise AssertionError((p,op,r,'fuel'))
  tested+=1
print('tested',tested,'late_one_events',len(records),'cases',len(set((r['pc'],r['positive']) for r in records)))
print('event_summary',counter)
Path(__file__).with_name('chain-contexts.json').write_text(json.dumps(records,indent=2))
for r in records[:25]:print(r)
