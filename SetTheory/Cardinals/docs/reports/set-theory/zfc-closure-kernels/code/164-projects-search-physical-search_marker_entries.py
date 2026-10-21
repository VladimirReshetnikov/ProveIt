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

T,start=ck.read(args.baseline);radius=7;fuel=97;I=ck.domain(T,start,radius)
Q=sorted({q for q,b in T});inc=defaultdict(list)
for row,(_,_,z) in T.items():inc[z].append(row)
counts=Counter();hits=[];beg=time.monotonic()
for keep,drop in itertools.combinations(Q,2):
 if start in (keep,drop) or len(inc[keep])!=1 or len(inc[drop])!=1:continue
 entries=[inc[keep][0],inc[drop][0]]
 if any(q in (keep,drop)for q,b in entries):continue
 common=[b for b in(0,1)if T[keep,b]==T[drop,b]]
 if len(common)!=1:continue
 fixed=common[0];other=1-fixed;counts['pairs']+=1
 N={k:(w,d,keep if z==drop else z)for k,(w,d,z)in T.items()if k[0]!=drop}
 patterns={row:sorted(m for m in I[row[0]]if((m>>radius)&1)==row[1]) for row in entries}
 for row,pp in patterns.items():
  if len(pp)>2:patterns[row]=[pp[0],pp[-1],*pp[1:-1]]
 paths={}
 def goals(row,m):
  key=row,m
  if key not in paths:
   oq,oh,om=row[0],0,m;out=set()
   for _ in range(fuel):
    if oq==254 or not -radius<=oh<=radius:break
    ob=(om>>(oh+radius))&1;ow,od,oq=T[oq,ob]
    om=(om&~(1<<(oh+radius)))|(ow<<(oh+radius));oh+=od
    if oq not in (keep,drop):out.add((oq,oh,om))
   paths[key]=out
  return paths[key]
 for mark0,mark1 in itertools.product(list(itertools.product((0,1),(-1,1))),repeat=2):
  N[entries[0]]=(*mark0,keep);N[entries[1]]=(*mark1,keep)
  N[keep,fixed]=T[keep,fixed]
  for act in itertools.product((0,1),(-1,1),[q for q in Q if q!=drop]+[254]):
   counts['specs']+=1;N[keep,other]=act;good=True
   for row in entries:
    if not good:break
    for m in patterns[row]:
     gg=goals(row,m);nq,nh,nm=row[0],0,m;visited=set();join=False
     for _ in range(fuel):
      if nq==254 or nq==drop or not -radius<=nh<=radius or (nq,nh,nm)in visited:break
      visited.add((nq,nh,nm));nb=(nm>>(nh+radius))&1;nw,nd,nq=N[nq,nb]
      nm=(nm&~(1<<(nh+radius)))|(nw<<(nh+radius));nh+=nd
      if (nq,nh,nm)in gg:join=True;break
     if not join:good=False;break
   if good:
    hit={'keep':keep,'drop':drop,'entries':[list(x)for x in entries],'marks':[mark0,mark1],'fixed':fixed,'act':act};hits.append(hit);print('HIT',hit,flush=True)
    (args.output/('entry-merge-'+str(len(hits))+'.tm')).write_bytes(fs.encode(N,start))
 if counts['pairs']%10==0:print('progress',dict(counts),time.monotonic()-beg,flush=True)
result={'radius':radius,'fuel':fuel,'counts':dict(counts),'hits':hits,'seconds':time.monotonic()-beg};(args.output/'marker-entry-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
