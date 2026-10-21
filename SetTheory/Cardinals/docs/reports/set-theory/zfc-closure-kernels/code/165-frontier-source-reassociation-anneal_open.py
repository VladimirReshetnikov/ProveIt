from pathlib import Path
code=(Path(__file__).parent/'open_rotations.py').read_text().split('\nout=Path(')[0]
exec(code)
import random,math,argparse
ap=argparse.ArgumentParser();ap.add_argument('--steps',type=int,default=40000);ap.add_argument('--seed',type=int,default=214);ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--output',type=Path);a=ap.parse_args();rng=random.Random(a.seed)
out=a.output or Path(__file__).parent/f'replay-open-anneal-{a.seed}';out.mkdir(parents=True,exist_ok=False)
best=202;root=R;current=202;chain=[];saved=[];stats=collections.Counter();started=time.monotonic()
for tick in range(a.steps):
 if time.monotonic()-started>a.seconds:break
 if tick%1500==0:
  root=R;current=202;chain=[]
 ns=list(node_set(root)); ns=[n for n in ns if not s.leaf(n)];n=rng.choice(ns);direction=rng.randrange(2)
 if s.leaf(n[direction]):continue
 if direction==0:(x,y),z=n;nn=(x,(y,z))
 else:x,(y,z)=n;nn=((x,y),z)
 cand=replacements(root,n,nn)
 try:cand,changes=repair(cand)
 except ValueError as e:stats['invalid_'+str(e)]+=1;continue
 val=len(node_set(cand));stats['valid']+=1
 temp=.20 if tick%1500<1200 else .45
 if val-current<=0 or rng.random()<math.exp(-(val-current)/temp):
  root=cand;current=val;chain.append({'before':n,'direction':direction,'after':nn,'retags':changes});stats['accepted']+=1
  if val<best:
   ss=s.sites(cand);cfg,check=s.graph_arithmetic(ss)
   assert cfg==G==s.graph_intervals(ss)
   best=val;name=f'candidate{len(saved):03d}';(out/(name+'.json')).write_bytes(s.compact(ss));(out/(name+'-recipe.json')).write_text(json.dumps(chain));saved.append({'name':name,'dag':best,'tick':tick,'chain':len(chain),'depth':max(len(p)for p,_,_ in ss)});print(json.dumps(saved[-1]),flush=True)
   if best<201:break
 if tick%1000==0:print(json.dumps({'tick':tick,'current':current,'best':best,'seconds':time.monotonic()-started,'stats':dict(stats)}),flush=True)
 node_set.cache_clear();size.cache_clear()
(out/'summary.json').write_text(json.dumps({'seed':a.seed,'tick':tick,'best':best,'saved':saved,'stats':dict(stats),'seconds':time.monotonic()-started},indent=2));print((out/'summary.json').read_text(),flush=True)
