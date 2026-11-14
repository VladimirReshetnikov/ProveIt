import sys,json,collections
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"verification"))
from core import *
d=json.load(open('experiments/variant.json'));rows={(q,b):(w,di,n)for q,b,w,di,n in d['rows']};labels=sorted({q for q,b in rows})+[254];sites=d['source_sites'];cs=[];RAD=12
for i,code in enumerate(d['instructions']):
 st=frame(sites[i][0])
 if code[0]=='inc':
  _,r,n=code;cs.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',PHYSICAL[r])))))
 elif code[0]=='dec':
  _,r,z,p=code;cs.append((i,(PHYSICAL[r],True),st,canonical(frame(sites[z][0]))))
  if i not in d['zero_constrained_sites']:cs.append((i,(PHYSICAL[r],False),st,canonical(frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
 elif code[0]=='jump':cs.append((i,None,st,canonical(frame(sites[code[1]][0]))))
 else:cs.append((i,None,st,None))

labs=labels
