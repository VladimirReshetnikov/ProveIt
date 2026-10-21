from pathlib import Path
code=(Path(__file__).parent/'open_rotations.py').read_text().split('\nout=Path(')[0];exec(code)
import random,math,argparse
ap=argparse.ArgumentParser();ap.add_argument('--steps',type=int,default=50000);ap.add_argument('--seed',type=int,default=51);ap.add_argument('--seconds',type=int,default=360);ap.add_argument('--output',type=Path);a=ap.parse_args();rng=random.Random(a.seed)
out=a.output or Path(__file__).parent/f'replay-zero-anneal-{a.seed}';out.mkdir(parents=True,exist_ok=False)
def risk(n):
 z=0;maxz=0
 def go(t,run):
  nonlocal z,maxz
  maxz=max(maxz,run)
  if s.leaf(t):return
  if run==5:z+=1
  go(t[0],run+1);go(t[1],0)
 go(n,0);return z,maxz
best=(99,999);root=R;current=202;rr,zz=risk(R);chain=[];saved=[];stats=collections.Counter();started=time.monotonic();score=202+rr*.14
for tick in range(a.steps):
 if time.monotonic()-started>a.seconds:break
 if tick%4000==0 and tick:
  root=R;current=202;rr,zz=risk(R);chain=[];score=202+rr*.14
 ns=[n for n in node_set(root) if not s.leaf(n)];n=rng.choice(ns);direction=rng.randrange(2)
 if s.leaf(n[direction]):continue
 if direction==0:(x,y),z=n;nn=(x,(y,z))
 else:x,(y,z)=n;nn=((x,y),z)
 try:cand,changes=repair(replacements(root,n,nn))
 except ValueError as e:stats['invalid_'+str(e)]+=1;continue
 val=len(node_set(cand));riskv,zv=risk(cand);value=val+.14*riskv+max(0,zv-6)*3;stats['valid']+=1
 temp=.22
 if value-score<=0 or rng.random()<math.exp(-(value-score)/temp):
  root=cand;current=val;rr,zz=riskv,zv;score=value;chain.append({'before':n,'direction':direction,'after':nn,'retags':changes});stats['accepted']+=1
  if val<=202 and (riskv,zv)<best:
   ss=s.sites(cand);cfg,check=s.graph_arithmetic(ss);assert cfg==G==s.graph_intervals(ss)
   best=(riskv,zv);name=f'candidate{len(saved):03d}';(out/(name+'.json')).write_bytes(s.compact(ss));(out/(name+'-recipe.json')).write_text(json.dumps(chain));saved.append({'name':name,'dag':val,'zero_risk':riskv,'maxzero':zv,'tick':tick,'chain':len(chain)});print(json.dumps(saved[-1]),flush=True)
   if riskv==0:break
 if tick%1000==0:print(json.dumps({'tick':tick,'current':current,'risk':rr,'maxzero':zz,'best':best,'seconds':time.monotonic()-started}),flush=True)
 node_set.cache_clear();size.cache_clear()
(out/'summary.json').write_text(json.dumps({'seed':a.seed,'tick':tick,'best':best,'saved':saved,'stats':dict(stats),'seconds':time.monotonic()-started},indent=2));print((out/'summary.json').read_text(),flush=True)
