from search_rotations import *
import math

def bad_mapping(t,root):
 visited=set();bad=set()
 def walk(n,p):
  if ll(n):return
  key=(n,p[-8:])
  if key in visited:return
  visited.add(key);q=n[0]
  for b in(0,1):
   if ll(n[b+1]):continue
   mem={i:int(x)for i,x in enumerate(p+str(b))};mem[-1]=1;orig=mem.copy();h=len(p);state=q
   for k in range(65):
    if h==len(p)+1 or h not in mem:break
    w,d,state=t[state,mem[h]];mem[h]=w;h+=d
   if mem!=orig or h!=len(p)+1 or state!=n[b+1][0]:bad.add((q,b,p[-3:]))
   walk(n[b+1],p+str(b))
 walk(root,'');return bad

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=5000);ap.add_argument('--seed',type=int,default=883);a=ap.parse_args()
 rng=random.Random(a.seed);base=t;base_lr=labeled(t,root);lr=base_lr
 history=[];bad=set();accepted=0;valid=0;tic=time.monotonic();out=Path(__file__).parent;seen=set();best=0
 for step in range(a.iterations):
  if step%150==0:t=base;lr=base_lr;history=[];bad=set()
  rs=rotations(t,lr)
  rot=rng.choice(rs);tt,lrr=rotate(t,lr,rot);key=tuple(sorted(tt.items()))
  if key in seen:continue
  seen.add(key)
  newbad=bad_mapping(tt,lrr)
  if len(newbad)>8 or (len(newbad)>len(bad)and rng.random()>math.exp((len(bad)-len(newbad))/1.0)):continue
  metrics=c.metrics(unlabel(lrr))
  if metrics['maximum_zero_run']>8:continue
  t,lr,bad=tt,lrr,newbad;history.append(rot);accepted+=1
  if not bad and metrics['maximum_zero_run']<=6:
   valid+=1;hits,score=folds(t)
   if score>best:
    best=score;print('BEST',step,'score',best,'history',history,flush=True)
    (out/f'best_relaxed_{a.seed}.tm').write_bytes(encode(t));c.dump(out/f'best_relaxed_{a.seed}_sites.json',c.sites(unlabel(lr)));c.dump(out/f'best_relaxed_{a.seed}_history.json',history)
   if valid%25==0:
    stamp=f'layout_{a.seed}_{step}';(out/(stamp+'.tm')).write_bytes(encode(t));c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_history.json'),history)
   if metrics['maximum_zero_run']<=5:
    stamp=f'zero5_{a.seed}_{step}';(out/(stamp+'.tm')).write_bytes(encode(t));c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_history.json'),history);print('ZERO5',history,flush=True)
    raise SystemExit
   for q0,q1,h0,h1 in hits:
    final={(q,b):(w,d,q1 if z==q0 else z)for(q,b),(w,d,z)in t.items()if q!=q0}
    final[q1,0]=(0,-1,h0);final[q1,1]=(1,-1,h1)
    proof=v.prove(t,final,0,0,q1,q0,0,None,8,65,20000)
    if proof['status'].startswith('PASS'):
     print('HIT',step,history,(q0,q1,h0,h1),flush=True)
     stamp=f'hit_relaxed_{a.seed}_{step}_{q0}_{q1}'
     (out/(stamp+'.tm')).write_bytes(encode(final));(out/(stamp+'_basis.tm')).write_bytes(encode(t))
     c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_proof.json'),proof);c.dump(out/(stamp+'_history.json'),history)
     raise SystemExit
  if step%100==0:print('PROGRESS',step,'accepted',accepted,'valid',valid,'bad',len(bad),'secs',time.monotonic()-tic,flush=True)
 print('DONE',a.iterations,'accepted',accepted,'valid',valid,'seen',len(seen),'secs',time.monotonic()-tic,flush=True)
