from pathlib import Path
import sys,json,itertools,time,collections,random,argparse
HERE=Path(__file__).resolve().parent.parent
PACKAGE=HERE.parents[1]
sys.path.insert(0,str(PACKAGE/'construction/vendor'));import symbolic_runtime as r
M=HERE/'inputs'
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'runs/orh_full');args=ap.parse_args()
B=args.output;B.mkdir(parents=True,exist_ok=True)
rows={}
for line in(M/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
sites=json.loads((M/'sites.json').read_text());ins=json.loads((M/'instructions.json').read_text());cs=[]
def frame(i,extra=0,effect=r.PLAIN):return r.frame(tuple(map(int,sites[i][0])),extra,effect)
def target(i,extra=0,effect=r.PLAIN):return r.canonical(frame(i,extra,effect))
for i,c in enumerate(ins):
 s=frame(i)
 if c[0]=='inc':_,n,j=c;cs.append((i,None,s,target(j,0,('x','inc',r.PHYSICAL[n]))))
 elif c[0]=='dec':_,n,z,j=c;cs.extend([(i,(r.PHYSICAL[n],True),s,target(z)),(i,(r.PHYSICAL[n],False),s,target(j,1,('x','dec',r.PHYSICAL[n])))] )
 elif c[0]=='jump':cs.append((i,None,s,target(c[1])))
 else:cs.append((i,None,s,None))
