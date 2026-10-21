#!/usr/bin/env python3
from pathlib import Path
from collections import defaultdict,Counter
import sys,itertools,json,time
sys.path.insert(0,str(Path(__file__).parent))
import check_joint_fold as ck
import filter_source as fs
import argparse, hashlib
cli=argparse.ArgumentParser(description=__doc__)
cli.add_argument('--baseline',type=Path,required=True)
cli.add_argument('--output',type=Path,required=True)
cli.add_argument('--variants',type=Path)
args=cli.parse_args()
if not __debug__:raise RuntimeError("Run without Python optimization")
assert hashlib.sha256(args.baseline.read_bytes()).hexdigest()=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088', 'Wrong K217 baseline'
args.output.mkdir(parents=True,exist_ok=True)

seed=args.baseline
T,start=ck.read(seed);radius=7;fuel=97;I=ck.domain(T,start,radius)
Q=sorted({q for q,b in T});incoming=defaultdict(list)
for row,(_,_,z) in T.items():incoming[z].append(row)
started=time.monotonic();hits=[];counts=Counter()
for drop in Q:
 if drop==start or len(incoming[drop])!=1:continue
 row=incoming[drop][0];q,b=row
 if q==drop:continue
 patterns=sorted(m for m in I[q] if ((m>>radius)&1)==b)
 if len(patterns)>2:patterns=[patterns[0],patterns[-1],*patterns[1:-1]]
 paths={}
 def path(m):
  if m not in paths:
   oq,oh,om=q,0,m;out=set()
   for _ in range(fuel):
    if oq==254 or not -radius<=oh<=radius:break
    ob=(om>>(oh+radius))&1;ow,od,oq=T[oq,ob]
    om=(om&~(1<<(oh+radius)))|(ow<<(oh+radius));oh+=od
    if oq!=drop:out.add((oq,oh,om))
   paths[m]=out
  return paths[m]
 N={k:v for k,v in T.items() if k[0]!=drop}
 for act in itertools.product((0,1),(-1,1),[z for z in Q if z!=drop]+[254]):
  counts['specifications']+=1;N[row]=act
  good=True
  for m in patterns:
   goals=path(m);nq,nh,nm=q,0,m;visited=set();joined=False
   for _ in range(fuel):
    if nq==254 or nq==drop or not -radius<=nh<=radius or (nq,nh,nm) in visited:break
    visited.add((nq,nh,nm));nb=(nm>>(nh+radius))&1;nw,nd,nq=N[nq,nb]
    nm=(nm&~(1<<(nh+radius)))|(nw<<(nh+radius));nh+=nd
    if (nq,nh,nm) in goals:joined=True;break
   if not joined:good=False;break
  if good:
   hit={'drop':drop,'row':row,'old_action':T[row],'action':act,'contexts':len(patterns)}
   hits.append(hit);print('HIT',hit,flush=True)
   (args.output/('bypass-'+str(drop)+'.tm')).write_bytes(fs.encode(N,start))
 counts['states']+=1
 if counts['states']%10==0:print('progress',dict(counts),time.monotonic()-started,flush=True)
result={'radius':radius,'fuel':fuel,'counts':dict(counts),'hits':hits,'seconds':time.monotonic()-started}
(args.output/'bypass-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
