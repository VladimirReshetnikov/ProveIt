from pathlib import Path
import sys,json,itertools,time,collections
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

T,start=ck.read(args.baseline);V={tuple(x['row']):{tuple(a)for a in x['actions']}for x in json.loads((args.variants if args.variants else Path(__file__).parent/'results'/'row-variants.json').read_text())};Q=sorted({q for q,b in T});I=ck.domain(T,start,7);oldpaths={};started=time.monotonic();counts=collections.Counter();hits=[]
helpervariants=[]
for h in Q:
 for a0,a1 in itertools.product(V[h,0],V[h,1]):
  if a0!=T[h,0]or a1!=T[h,1]:helpervariants.append((h,a0,a1))
for keep,drop in itertools.combinations(Q,2):
 common=[b for b in(0,1)if T[keep,b]==T[drop,b]]
 if len(common)!=1 or 0 in(keep,drop):continue
 counts['pairs']+=1;other=1-common[0];phi=lambda q:keep if q==drop else q
 base={k:(w,d,phi(z))for k,(w,d,z)in T.items()if k[0]!=drop}
 for h,a0,a1 in helpervariants:
  if h in(keep,drop):continue
  N=base.copy();N[h,0]=(a0[0],a0[1],phi(a0[2]));N[h,1]=(a1[0],a1[1],phi(a1[2]))
  for w,d in itertools.product((0,1),(-1,1)):
   N[keep,other]=(w,d,h);counts['specifications']+=1
   fail=fs.local_filter(T,N,I,keep,drop,oldpaths,97,7)
   if fail is not None:continue
   counts['local_passes']+=1;spec={'keep':keep,'drop':drop,'branch':other,'helper':h,'rows':[a0,a1],'action':[w,d,h]};print('LOCAL',spec,flush=True)
   try:proof=ck.check(T,N,start,start,keep,drop,7,97,I)
   except ValueError as e:counts['global_failures']+=1;print('GLOBALFAIL',str(e),flush=True);continue
   hits.append({'spec':spec,'proof':proof});(args.output/('helper-rewrite-hit-'+str(len(hits))+'.tm')).write_bytes(fs.encode(N,start));print('HIT',spec,flush=True)
 if counts['pairs']%25==0:print('PROGRESS',dict(counts),time.monotonic()-started,flush=True)
 if time.monotonic()-started>240:break
out={'counts':dict(counts),'hits':hits,'seconds':time.monotonic()-started};(args.output/'helper-rewrite-results.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',out)
