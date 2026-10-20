from pathlib import Path
import random,json,time,sys
sys.path.insert(0,str(Path(__file__).parent))
import rot_full
from inv_fold import load
namespace={"__file__":str(Path("rotations/rot_fold_search.py").resolve())}
exec(Path('rotations/rot_fold_search.py').read_text().split('def main():')[0],namespace)
folds=namespace['fast_folds']
P=Path('/workspace/scratch/32bd1523fdcd/baseline219/K219_Construction_2026-10-20/machine')
T0,st=load(P/'k219.native.tm');S0=json.loads((P/'sites219.json').read_text());rng=random.Random(218313);start=time.monotonic()
out=Path('rotations/walk_results');out.mkdir(exist_ok=True);hits=0;visited=set();T,S=T0,S0;chain=[]
for it in range(2500):
 if it%100==0:T,S=T0,S0;chain=[]
 choices=list(rot_full.rotations(T,S,7))
 if not choices:continue
 unseen=[c for c in choices if tuple(sorted(c[1].items()))not in visited]
 tag,N,SS,z=rng.choice(unseen or choices)
 T,S=N,SS;chain.append(tag);visited.add(tuple(sorted(T.items())))
 if z<=6:
  duplicate={};plans=[]
  for q in sorted({q for q,c in T}):
   sig=(T[q,0],T[q,1])
   if sig in duplicate:plans.append((duplicate[sig],q,{0:'same',1:'same'}))
   duplicate[sig]=q
  plans+=folds(T,st,8,9)
  if len(T)<len(T0):plans.append((None,None,{}))
  for keep,drop,plan in plans:
   hits+=1;nm=f'hit{hits:03d}';M={k:(w,d,keep if z==drop else z)for k,(w,d,z)in T.items()if k[0]!=drop}
   for c,p in plan.items():
    if isinstance(p,tuple):M[keep,c]=p
   (out/(nm+'.tm')).write_text('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(M.items())))
   (out/(nm+'.sites.json')).write_text(json.dumps(S,separators=(',',':'))+'\n')
   (out/(nm+'.json')).write_text(json.dumps({'iteration':it,'chain':chain,'keep':keep,'drop':drop,'plan':plan},indent=2))
   print('HIT',nm,'iter',it,'states',len(M)//2,'plan',keep,drop,plan,flush=True)
 if it%100==0:print('ITER',it,'hits',hits,'seconds',round(time.monotonic()-start,1),flush=True)
