from pathlib import Path
import argparse,collections,hashlib,json,random,sys,time
sys.dont_write_bytecode=True
import search_directional as D
L=D.L

def digest(t):return hashlib.sha256(D.S.encode(t).encode()).digest()
def run(label,maxdepth,width):
 b=D.I.base
 if label=='A':tp=b/'machine/variant_plain/u208.native.tm';sp=b/'machine/variant_plain/u208.sites.json'
 else:tp=b/'machine/u208.native.tm';sp=b/'machine/u208.sites.json'
 t=D.I.read(tp);ss=json.loads(sp.read_text());root=L.tree(ss);seen={digest(t)};frontier=[];results=[];rng=random.Random(93278)
 out=D.S.work/('connected_'+label);out.mkdir(exist_ok=True);D.out=out
 seeds=D.enum(t,root)
 if label=='A':seeds=[r for r in seeds if r in[(225,210,1),(84,189,0),(189,145,0),(38,53,1)]]
 for seed in seeds:
  nt,nr=D.rotate(t,root,seed);seen.add(digest(nt));frontier.append((seed,nt,nr,[seed],set(seed[:2])))
 began=time.monotonic()
 for depth in range(2,maxdepth+1):
  buckets=collections.defaultdict(list)
  for seed,t,r,hist,active in frontier:
   for rot in D.enum(t,r):
    if not set(rot[:2])&active:continue
    nt,nr=D.rotate(t,r,rot);k=digest(nt)
    if k in seen:continue
    seen.add(k);nh=hist+[rot];mt,folds=D.S.merge(nt)
    if folds:
     rec=D.test(mt,nr,nh,folds,len(results));results.append(rec)
     if rec['pass']:
      print('FOUND_FINITE',label,rec,flush=True)
    # Keep prefold table even after a rejected identical-state collapse.
    # Rank source syntax sharing with random tie-breaking; reject no intermediate by runtime.
    dag=L.metrics(nr)['dag_nodes']
    rank=(dag,rng.random())
    buckets[seed].append((rank,seed,nt,nr,nh,active|set(rot[:2])))
  frontier=[]
  for seed,items in buckets.items():
   items.sort(key=lambda x:x[0]);frontier.extend(x[1:]for x in items[:width])
  print('DEPTH',label,depth,'frontier',len(frontier),'seen',len(seen),'folds',len(results),'seconds',time.monotonic()-began,flush=True)
  (out/'progress.json').write_text(json.dumps({'label':label,'depth':depth,'seen':len(seen),'frontier':len(frontier),'candidate_count':len(results),'results':results},indent=2)+'\n')
  if not frontier:break
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('label');p.add_argument('--depth',type=int,default=10);p.add_argument('--width',type=int,default=8);a=p.parse_args();run(a.label,a.depth,a.width)
