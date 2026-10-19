from explore import *
from check_literal_instructions import program_sites,paint,expected
import json
sites=program_sites(BASE/'sources/Prog254.v');t=T|{(75,0):(0,-1,112)}
for kind in ['CI','CD']:
 for pc,k,r in [s for s in sites if s[1]==kind][:3]:
  for value in ([0,3] if kind=='CD' else [0]):
   vs=[0]*9;from check_literal_instructions import PHYSICAL
   vs[PHYSICAL[r]]=value;sp=[0];one=paint(pc,40,vs,sp,0);h=0;q=96
   seen=[]
   for steps in range(2000):
    w,d,q=t[q,int(h in one)]
    if w:one.add(h)
    else:one.discard(h)
    h+=d
    if q==96:
     target=expected(pc,k,r,vs,sp,0,40)
     # parse frame shifted file and arbitrary spares
     h0=target[0];span=target[3]-(k=='CI');ns=target[5][:-1]+[0] if k=='CI' else target[5]
     want=paint(target[2],span,target[4],ns,h0)
     seen.append((steps+1,h,h==h0 and one==want,sorted(one^want)[:30]))
     if len(seen)>2 or one==want:break
   print(pc,k,r,value,seen)
