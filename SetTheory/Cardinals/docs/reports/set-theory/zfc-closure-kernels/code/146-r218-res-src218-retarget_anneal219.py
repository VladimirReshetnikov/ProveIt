#!/usr/bin/env python3
"""K219 source reassociation search; costs are exploratory, never certificates.

Unlike the K220 search, an old logical node may have two physical decoder
roles.  Both are retained in the cost model.  Local rotations retarget outward
CB/CC arguments and preserve every implicit CD branch target.
"""
from pathlib import Path
from functools import cache
from collections import defaultdict,Counter
import argparse,hashlib,json,math,random,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'))
import rotation_search as r
from hardware_objective219 import model
s,b=r.s,r.b
ap=argparse.ArgumentParser()
ap.add_argument('--iterations',type=int,default=300000)
ap.add_argument('--seed',type=int,default=218)
ap.add_argument('--start',type=Path,default=ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json')
ap.add_argument('--output',type=Path,default=ROOT/'source218/retarget_candidates')
ap.add_argument('--selective',action='store_true')
ap.add_argument('--max-cc',type=int,default=3)
ap.add_argument('--commute',action='store_true')
ap.add_argument('--free-bootstrap',action='store_true')
ap.add_argument('--max-zero-run',type=int,default=6)
ap.add_argument('--target-states',type=int,default=218)
ap.add_argument('--semantic-reference',type=Path)
a=ap.parse_args()
p=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
T=b.read_table((p/'k219.native.tm').read_bytes())
original=r.normalise(s.tree(json.loads((p/'sites219.json').read_text())))
evaluate,meta=model(T,original,json.loads((ROOT/'source218/frozen_engine_rows219.json').read_text())['rows'])
vals=[];ids={};met=[];bad=[];wordhash=[]
word_powers=[1]
for i in range(5000):word_powers.append((word_powers[-1]*1000003)&((1<<64)-1))
def intern(n):
 if n in ids:return ids[n]
 k=len(vals);ids[n]=k;vals.append(n)
 if isinstance(n[0],str):
  met.append((1,0,0,0));bad.append((0,)*(a.max_zero_run+1))
  wordhash.append(32*dict(CI=1,CD=2,CB=3,CC=4,CH=5)[n[0]]+((n[1]or 0)if n[0]in('CI','CD','CH')else 0))
 else:
  A,B=n;al,alead,az,ah=met[A];bl,blead,bz,bh=met[B];lead=1+alead
  met.append((al+bl,lead,max(lead,az,bz),1+max(ah,bh)))
  bad.append(tuple((bad[A][z+1]if z<a.max_zero_run else al)+bad[B][0]for z in range(a.max_zero_run+1)))
  wordhash.append((wordhash[A]*word_powers[bl]+wordhash[B])&((1<<64)-1))
 return k
@cache
def encode(n):return intern(n)if s.leaf(n)else intern((encode(n[0]),encode(n[1])))
ORIGINALROOT=encode(original)
BASE=encode(s.tree(json.loads(a.start.read_text())))
state_nodes={q:{encode(n)for n in ns}for q,ns in meta['groups'].items()}
node_states={encode(n):qs for n,qs in meta['node_states'].items()}
protected=meta['protected'];qprotected=meta['protected_states'];nondecoder=meta['nondecoder']
leafactions=defaultdict(set)
for (leaf,bit),acts in meta['leaves'].items():leafactions[encode(leaf),bit].update(acts)
# Existing selectors reached through K219's new generalized zero return.
for arg,q in [(1,41),(3,17),(4,144),(5,45),(6,21)]:
 leafactions[encode(('CD',arg)),1].add((1,1,q))
keep=len(vals)
@cache
def requirements(q,n):
 if n in node_states:return ()if q in node_states[n]else None
 if isinstance(vals[n][0],str)or q not in state_nodes:return None
 pairs={q:n};inverse={n:q}
 for bit,ch in enumerate(vals[n]):
  if(q,bit)not in protected:continue
  act=T[q,bit]
  if isinstance(vals[ch][0],str):
   if act not in leafactions[ch,bit]:return None
  else:
   if act[:2]!=(bit,1):return None
   req=requirements(act[2],ch)
   if req is None:return None
   for st,node in req:
    if st in pairs and pairs[st]!=node:return None
    if node in inverse and inverse[node]!=st:return None
    pairs[st]=node;inverse[node]=st
 return tuple(pairs.items())
def hardware_score(ls,current_root):
 fixed=set().union(*(node_states.get(n,())for n in ls))
 fresh=[n for n in ls if not isinstance(vals[n][0],str)and n not in node_states]
 missing=qprotected-fixed;candidate={}
 for q in missing:
  opts=[]
  for n in fresh:
   if n==current_root and q!=84:continue
   req=requirements(q,n)
   if req is not None and all(st not in fixed for st,node in req):opts.append(n)
  candidate[q]=opts
 matched={}
 def augment(q,seen):
  for n in candidate[q]:
   if n in seen:continue
   seen.add(n)
   if n not in matched or augment(matched[n],seen):matched[n]=q;return True
  return False
 for q in sorted(candidate,key=lambda q:len(candidate[q])):augment(q,set())
 return nondecoder+len(fixed)+len(fresh)+len(missing)-len(matched)
def child_key(key,bit):
 v=(key<<1)|bit
 return v if key<256 else 256|(v&255)
@cache
def edge(q,bit,targets,key):
 suffix=bin(key)[3:];tape={i-len(suffix):int(v)for i,v in enumerate(suffix)};tape[0]=bit
 before=dict(tape);head=0
 for tick in range(100):
  if head==1:return int(q not in targets or tape!=before)
  if head not in tape or(q,tape[head])not in T:return 1
  w,d,q=T[q,tape[head]];tape[head]=w;head+=d
 return 1
@cache
def own_penalty(n,key):
 if n not in node_states:return 0
 suffix=bin(key)[3:];choices=[]
 for q in node_states[n]:
  v=0
  for bit,ch in enumerate(vals[n]):
   if not isinstance(vals[ch][0],str):v+=edge(q,bit,node_states[ch],key)
   elif q==108 and bit==1:
    leaf_suffix=suffix+'1'
    if vals[ch]==('CC',2):v+=int(not leaf_suffix.endswith('101'))
    elif vals[ch]==('CB',1):v+=int(not leaf_suffix.endswith('001'))
  choices.append(v)
 return min(choices)
@cache
def context(n,key=3):
 if isinstance(vals[n][0],str):
  if vals[n]==('CC',4):return int(not bin(key)[3:].endswith('1111'))
  return 0
 return own_penalty(n,key)+context(vals[n][0],child_key(key,0))+context(vals[n][1],child_key(key,1))
def live(q):
 seen={q};todo=[q]
 for k in todo:
  n=vals[k]
  if isinstance(n[0],str):continue
  for v in n:
   if v not in seen:seen.add(v);todo.append(v)
 return seen
def score(q,ls):
 if not a.free_bootstrap and vals[q][0]!=vals[ORIGINALROOT][0]:return(999,999,999)
 cost=hardware_score(ls,q);pen=context(q)
 return cost+max(0,met[q][2]-a.max_zero_run)*1.05+min(.25,bad[q][0]*.005)+max(0,met[q][3]-50)*.2+.18*pen,cost,pen
def rewrite(root,old,new):
 memo={old:new}
 def go(k):
  if k in memo:return memo[k]
  n=vals[k];v=k if isinstance(n[0],str)else intern((go(n[0]),go(n[1])));memo[k]=v;return v
 return go(root)
@cache
def adjust(k,op,delta,depth=0):
 n=vals[k]
 if isinstance(n[0],str):
  code,arg=n
  if op=='CB'and code=='CD'and depth==0:return None
  if code!=op or arg<=depth:return k
  if delta<0 and arg-depth==1:return None
  arg+=delta
  if not 1<=arg<=(1 if op=='CB'else a.max_cc):return None
  return intern((code,arg))
 if depth>=a.max_cc:return k
 x=adjust(n[0],op,delta,depth+(op=='CB'))
 if x is None:return None
 y=adjust(n[1],op,delta,depth+(op=='CC'))
 return None if y is None else intern((x,y))
@cache
def local_alternatives(k):
 n=vals[k];ans=[]
 if isinstance(n[0],str):return ()
 A,B=n
 if not isinstance(vals[B][0],str):
  C,D=vals[B];aa=adjust(A,'CB',1);dd=adjust(D,'CC',-1)
  if aa is not None and dd is not None:ans.append(intern((intern((aa,C)),dd)))
 if not isinstance(vals[A][0],str):
  C,D=vals[A];cc=adjust(C,'CB',-1);bb=adjust(B,'CC',1)
  if cc is not None and bb is not None:ans.append(intern((cc,intern((D,bb)))))
 return tuple(ans)
def alternatives(ls):
 ans=[(k,n)for k in ls for n in local_alternatives(k)]
 if a.commute:
  for k in ls:
   n=vals[k]
   if not isinstance(n[0],str)and vals[n[0]][0]=='CI'and vals[n[1]][0]=='CI'and n[0]!=n[1]:ans.append((k,intern((n[1],n[0]))))
 if not a.selective:return ans
 parents={k:[]for k in ls}
 for p in ls:
  if not isinstance(vals[p][0],str):
   for bit,ch in enumerate(vals[p]):parents[ch].append((p,bit))
 more=[]
 for k,n in ans:
  for p,bit in parents[k]:
   children=list(vals[p]);children[bit]=n;pn=intern(tuple(children));more.append((p,pn))
   if len(parents[k])>1:
    for gp,gb in parents[p]:
     children=list(vals[gp]);children[gb]=pn;more.append((gp,intern(tuple(children))))
 return ans+more
def decode(q):
 memo={}
 def go(k):
  if k in memo:return memo[k]
  n=vals[k];v=n if isinstance(n[0],str)else(go(n[0]),go(n[1]));memo[k]=v;return v
 return go(q)
oldrows=json.loads(a.semantic_reference.read_text())if a.semantic_reference else s.sites(original)
oldcfg=s.graph_arithmetic(oldrows)[0]
incoming=defaultdict(set)
for i,rec in enumerate(oldcfg):
 for target in rec[1]:incoming[target].add(i)
ci_runs=[];run=[]
for i,row in enumerate(oldrows):
 if row[1]=='CI':
  if run and incoming[i]!={i-1}:ci_runs.append(run);run=[]
  run.append(i)
 elif run:ci_runs.append(run);run=[]
if run:ci_runs.append(run)
def commute_check(rows):
 if not a.commute:return [(x[1],x[2]if x[1]in('CI','CD','CH')else None)for x in rows]==[(x[1],x[2]if x[1]in('CI','CD','CH')else None)for x in oldrows]
 if any(x[1]!=y[1]or(x[1]in('CD','CH')and x[2]!=y[2])for x,y in zip(rows,oldrows)):return False
 return all(Counter(rows[i][2]for i in run)==Counter(oldrows[i][2]for i in run)for run in ci_runs)
def checked_bytes(q):
 tree=decode(q);rows=s.sites(tree)
 assert commute_check(rows)
 graph=s.graph_arithmetic(rows)[0];assert graph==s.graph_intervals(rows)
 assert [x[1]for x in graph]==[x[1]for x in oldcfg]
 return tree,s.compact(rows)
rng=random.Random(a.seed);q=BASE;ls=live(q);sc=score(q,ls);best=sc[0]
elite=[BASE];hits=[];seen=set();neutral_seen=set();start=time.monotonic();a.output.mkdir(exist_ok=True,parents=True)
assert hardware_score(live(ORIGINALROOT),ORIGINALROOT)==219
assert context(ORIGINALROOT)==0
print('INITIAL',sc,'protected',len(protected),'decoder',len(state_nodes),'seconds',0,flush=True)
for i in range(a.iterations):
 if i%4000==0:
  q=BASE if rng.random()<.2 else rng.choice(elite);ls=live(q);sc=score(q,ls)
 choices=alternatives(ls)
 if not choices:break
 old,new=rng.choice(choices);qq=rewrite(q,old,new)
 if a.commute and wordhash[old]!=wordhash[new]and not commute_check(s.sites(decode(qq))):continue
 ll=live(qq);ss=score(qq,ll)
 temp=.10+.5*(1-(i%4000)/4000)**2
 if ss[1]<=222 and ss[0]<=best+2.1 and(ss[0]<=sc[0]or rng.random()<math.exp(min(0,(sc[0]-ss[0])/temp))):
  q,ls,sc=qq,ll,ss
  if sc[0]<best:
   best=sc[0];elite=[q];tree,sourcebytes=checked_bytes(q)
   (a.output/'best_sites.json').write_bytes(sourcebytes)
   (a.output/'best_metrics.json').write_text(json.dumps(dict(iteration=i,score=sc,metrics=s.metrics(tree),bad_leaves=bad[q][0]),indent=2)+'\n')
   print('BEST',i,'score',sc,'dag',len(ls),'zero',met[q][2],'bad',bad[q][0],'depth',met[q][3],flush=True)
  elif sc[0]==best and rng.random()<.03:
   elite.append(q)
   if len(elite)>60:elite.pop(1)
  if sc[1]<=219 and met[q][2]<=a.max_zero_run and sc[2]==0 and rng.random()<.01:
   tree,sourcebytes=checked_bytes(q);digest=hashlib.sha256(sourcebytes).hexdigest()
   if digest not in neutral_seen:
    folder=a.output/'neutral'/f'v{len(neutral_seen):05d}';folder.mkdir(exist_ok=True,parents=True);neutral_seen.add(digest)
    (folder/'sites.json').write_bytes(sourcebytes)
    (folder/'receipt.json').write_text(json.dumps(dict(iteration=i,estimated_cost=sc[1],source_sha256=digest,metrics=s.metrics(tree),compile_pending=True))+'\n')
  if sc[1]<=a.target_states and met[q][2]<=a.max_zero_run and met[q][3]<=64 and sc[2]==0:
   tree,sourcebytes=checked_bytes(q);digest=hashlib.sha256(sourcebytes).hexdigest()
   if digest not in seen:
    seen.add(digest);folder=a.output/f'v{len(hits):04d}';folder.mkdir(exist_ok=True)
    record=dict(iteration=i,estimated_cost=sc[1],metrics=s.metrics(tree),compile_pending=True)
    (folder/'sites.json').write_bytes(sourcebytes);(folder/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    hits.append(record);print('HIT',str(folder),record,flush=True)
 if i%10000==0:print('PROGRESS',i,'score',sc,'best',best,'interned',len(vals),'seconds',round(time.monotonic()-start,1),flush=True)
 if i and i%2000==0:
  context.cache_clear();own_penalty.cache_clear();requirements.cache_clear();adjust.cache_clear();local_alternatives.cache_clear()
  prior=vals[:];vals[:]=vals[:keep];met[:]=met[:keep];bad[:]=bad[:keep];wordhash[:]=wordhash[:keep]
  ids.clear();ids.update({n:k for k,n in enumerate(vals)});memo={k:k for k in range(keep)}
  def rebuild(k):
   if k in memo:return memo[k]
   n=prior[k];v=intern(n)if isinstance(n[0],str)else intern((rebuild(n[0]),rebuild(n[1])));memo[k]=v;return v
  q=rebuild(q);elite=[rebuild(k)for k in elite];ls=live(q)
 (a.output/'summary.json').write_text(json.dumps(dict(iterations=i+1,best=best,hits=hits,neutral_sources=len(neutral_seen),seconds=time.monotonic()-start),indent=2)+'\n') if i%10000==0 else None
(a.output/'summary.json').write_text(json.dumps(dict(iterations=i+1,best=best,hits=hits,neutral_sources=len(neutral_seen),seconds=time.monotonic()-start),indent=2)+'\n')
