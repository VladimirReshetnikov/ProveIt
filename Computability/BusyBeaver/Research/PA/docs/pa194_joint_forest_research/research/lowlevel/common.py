from pathlib import Path
import sys,json,itertools,time,collections,random
B=Path(__file__).parent;sys.path.insert(0,str(B/'baseline'));import symbolic_runtime as r
labels=json.loads((B/'baseline/tables/pa194.labels.json').read_text());rows={}
for line in (B/'baseline/tables/pa194.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=int(w),d=='R',labels[int(n)]
sites=json.loads((B/'baseline/source/pa194.sites.json').read_text());ins=json.loads((B/'baseline/source/pa194.instructions.json').read_text());cs=[]
def frame(i,extra=0,effect=r.PLAIN):return r.frame(tuple(map(int,sites[i][0])),extra,effect)
def target(i,extra=0,effect=r.PLAIN):return r.canonical(frame(i,extra,effect))
for i,c in enumerate(ins):
 s=frame(i)
 if c[0]=='inc':_,n,j=c;cs.append((i,None,s,target(j,0,('x','inc',r.PHYSICAL[n]))))
 elif c[0]=='dec':_,n,z,j=c;cs.extend([(i,(r.PHYSICAL[n],True),s,target(z)),(i,(r.PHYSICAL[n],False),s,target(j,1,('x','dec',r.PHYSICAL[n])))] )
 elif c[0]=='jump':cs.append((i,None,s,target(c[1])))
 else:cs.append((i,None,s,None))
