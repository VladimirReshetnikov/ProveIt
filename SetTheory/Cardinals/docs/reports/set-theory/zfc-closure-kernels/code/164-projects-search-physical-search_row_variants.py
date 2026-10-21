from pathlib import Path
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).parent))
import check_joint_fold as ck
import argparse, hashlib
cli=argparse.ArgumentParser(description=__doc__)
cli.add_argument('--baseline',type=Path,required=True)
cli.add_argument('--output',type=Path,required=True)
cli.add_argument('--variants',type=Path)
args=cli.parse_args()
if not __debug__:raise RuntimeError("Run without Python optimization")
assert hashlib.sha256(args.baseline.read_bytes()).hexdigest()=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088', 'Wrong K217 baseline'
args.output.mkdir(parents=True,exist_ok=True)

T,start=ck.read(args.baseline);r=7;fuel=97;I=ck.domain(T,start,r);Q=sorted({q for q,b in T});out=[];started=time.monotonic();total=0
for row in sorted(T):
 q,b=row;pp=sorted(m for m in I[q]if ((m>>r)&1)==b)
 if len(pp)>2:pp=[pp[0],pp[-1],*pp[1:-1]]
 cache={}
 def goals(m):
  if m not in cache:
   oq,oh,om=q,0,m;gg=set()
   for _ in range(fuel):
    if oq==254 or not -r<=oh<=r:break
    ob=(om>>(oh+r))&1;ow,od,oq=T[oq,ob];om=(om&~(1<<(oh+r)))|(ow<<(oh+r));oh+=od;gg.add((oq,oh,om))
   cache[m]=gg
  return cache[m]
 acts=[]
 for act in itertools.product((0,1),(-1,1),Q+[254]):
  if act==T[row]:acts.append(act);continue
  good=True
  for m in pp:
   gg=goals(m);nq,nh,nm=q,0,m;visited=set();join=False
   for _ in range(fuel):
    if nq==254 or not -r<=nh<=r or (nq,nh,nm)in visited:break
    visited.add((nq,nh,nm));nb=(nm>>(nh+r))&1;nw,nd,nz=act if (nq,nb)==row else T[nq,nb];nm=(nm&~(1<<(nh+r)))|(nw<<(nh+r));nh+=nd;nq=nz
    if (nq,nh,nm)in gg:join=True;break
   if not join:good=False;break
  if good:acts.append(act)
 out.append({'row':row,'old':T[row],'actions':acts,'contexts':len(pp)});total+=len(acts)-1
 if len(out)%40==0:print('PROGRESS',len(out),'alternatives',total,'seconds',time.monotonic()-started,flush=True)
 if len(acts)>1:print('OPTIONS',row,acts,flush=True)
(args.output/'row-variants.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',len(out),total,time.monotonic()-started)
