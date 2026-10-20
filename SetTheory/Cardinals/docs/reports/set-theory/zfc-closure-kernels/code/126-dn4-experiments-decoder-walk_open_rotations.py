from general_rotations import *
import math
ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=3000);ap.add_argument('--seed',type=int,default=12413);a=ap.parse_args()
p=Path(__file__).parent/'dn4_open_rotations';out=Path(__file__).parent/'open_walk';out.mkdir(exist_ok=True)
seeds=[]
for rec in json.loads((p/'representative_probes.json').read_text()):
 if rec['status']!='PASS_REPRESENTATIVE_CASES':continue
 name=rec['name'];t,_=v.parse_table((p/(name+'.tm')).read_bytes());r=c.tree(json.loads((p/(name+'_sites.json')).read_text()));seeds.append((t,labeled(t,r),name))
rng=random.Random(a.seed);tt,lr,name=rng.choice(seeds);basegraph=c.graph_arithmetic(c.sites(unlabel(lr)));hist=[];seen=set();accepted=0;best=0;tic=time.monotonic();stats=collections.Counter()
for step in range(a.iterations):
 if step%120==0:tt,lr,name=rng.choice(seeds);hist=[]
 rs=moves(tt,lr,len(tt)//2<=225)
 if not rs:continue
 rot=rng.choice(rs);u,ur=perform(tt,lr,rot);key=tuple(sorted(u.items()))
 if key in seen:continue
 seen.add(key)
 r=unlabel(ur)
 try:
  if c.graph_arithmetic(c.sites(r))!=basegraph:stats['graph']+=1;continue
 except Exception:stats['invalid_graph']+=1;continue
 if bad_mapping(u,ur):stats['prefix']+=1;continue
 metrics=c.metrics(r)
 if metrics['maximum_zero_run']>6:stats['zero7']+=1;continue
 u,ur,rec=probe_folds(u,ur);n=len(u)//2
 if n>226:continue
 if n>len(tt)//2 and rng.random()>0.18:continue
 # Keep the engine q38/0 behavior unchanged; its secondary CI8 use is known.
 if u.get((38,0))!=(0,1,13):stats['known_helper_conflict']+=1;continue
 tt,lr=u,ur;hist.append(dict(rotation=rot,folds=rec['folds'],gc={k:z for k,z in rec['gc'].items()if k!='mapping'}));accepted+=1
 if rec['score']>best and n<=225:
  best=rec['score'];print('BEST',step,n,best,'seed',name,'depth',len(hist),flush=True)
  (out/'best.tm').write_bytes(encode(tt));c.dump(out/'best_sites.json',c.sites(unlabel(lr)));c.dump(out/'best_recipe.json',dict(seed=name,history=hist))
 if n<=224 or(n<=225 and metrics['maximum_zero_run']<=5):
  path=out/f'HIT_{a.seed}_{step}';path.with_suffix('.tm').write_bytes(encode(tt));c.dump(path.with_name(path.name+'_sites.json'),c.sites(unlabel(lr)));c.dump(path.with_name(path.name+'_recipe.json'),dict(seed=name,history=hist));print('HIT',step,n,name,len(hist),flush=True);break
 if step%100==0:print('PROGRESS',step,'accepted',accepted,'n',n,'score',rec['score'],'secs',time.monotonic()-tic,flush=True)
else:print('DONE',a.iterations,'accepted',accepted,'seen',len(seen),'stats',dict(stats),'secs',time.monotonic()-tic,flush=True)
