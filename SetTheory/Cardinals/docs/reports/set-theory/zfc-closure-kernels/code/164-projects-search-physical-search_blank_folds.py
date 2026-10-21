from pathlib import Path
from collections import deque,Counter
import sys,itertools,json,time
sys.path.insert(0,str(Path(__file__).parent));import check_joint_fold as ck;import filter_source as fs
import argparse, hashlib
cli=argparse.ArgumentParser(description=__doc__)
cli.add_argument('--baseline',type=Path,required=True)
cli.add_argument('--output',type=Path,required=True)
cli.add_argument('--variants',type=Path)
args=cli.parse_args()
if not __debug__:raise RuntimeError("Run without Python optimization")
assert hashlib.sha256(args.baseline.read_bytes()).hexdigest()=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088', 'Wrong K217 baseline'
args.output.mkdir(parents=True,exist_ok=True)

T,start=ck.read(args.baseline);r=7;mask=(1<<15)-1;I={q:set()for q,b in T};I[254]=set();I[start].add(0);todo=deque([(start,0)])
while todo:
 q,m=todo.popleft()
 if q==254:continue
 w,d,z=T[q,(m>>r)&1];x=(m&~(1<<r))|(w<<r)
 if d==1:a=x>>1;pp=(a,a|(1<<14))
 else:a=(x<<1)&mask;pp=(a,a|1)
 for n in pp:
  if n not in I[z]:I[z].add(n);todo.append((z,n))
Q=sorted({q for q,b in T});paths={};counts=Counter();hits=[];beg=time.monotonic()
for keep,drop in itertools.permutations(Q,2):
 counts['pairs']+=1;phi=lambda q:keep if q==drop else q;N={k:(w,d,phi(z))for k,(w,d,z)in T.items()if k[0]!=drop}
 aa=[{(T[q,b][0],T[q,b][1],phi(T[q,b][2]))for q in(keep,drop)}for b in(0,1)];common=[b for b in(0,1)if len(aa[b])==1];variants=list(itertools.product(*aa))
 if len(common)==1:
  fixed=common[0];other=1-fixed
  for act in itertools.product((0,1),(-1,1),[q for q in Q if q!=drop]+[254]):
   if act in aa[other]:continue
   both=[None,None];both[fixed]=next(iter(aa[fixed]));both[other]=act;variants.append(tuple(both))
 for a0,a1 in variants:
  counts['specifications']+=1;N[keep,0]=a0;N[keep,1]=a1
  if fs.local_filter(T,N,I,keep,drop,paths,97,7)is not None:continue
  try:proof=ck.check(T,N,start,phi(start),keep,drop,7,97,I)
  except ValueError:continue
  proof['scope']='Matching positive diagrams on an inductive window domain initialized by the all-zero radius7 window; arbitrary exterior tapes, hence includes blank tape. No all-initial-tape claim.'
  hit={'keep':keep,'drop':drop,'rows':[a0,a1],'proof':proof};hits.append(hit);(args.output/('blank-fold-hit-'+str(len(hits))+'.tm')).write_bytes(fs.encode(N,phi(start)));print('HIT',hit,flush=True)
 if counts['pairs']%10000==0:print('PROGRESS',dict(counts),time.monotonic()-beg,flush=True)
res={'scope':'inductive windows from zero radius7 window, arbitrary exterior','counts':dict(counts),'hits':hits,'seconds':time.monotonic()-beg};(args.output/'blank-fold-results.json').write_text(json.dumps(res,indent=2)+'\n');print('DONE',res)
