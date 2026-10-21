#!/usr/bin/env python3
"""General two-action folds with multi-step joins in symmetric windows."""
import argparse,json,collections,itertools,time,hashlib,functools
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--radius',type=int,default=3);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
T={};start=None
for line in a.table.read_text().splitlines():
 if line.startswith('#! start '):start=int(line[9:]);continue
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
S=sorted({q for q,b in T});k=a.radius;nbits=2*k+1;mask=(1<<nbits)-1;center=1<<k;domain={q:set()for q in S};Q=collections.deque()
for word in range(1<<nbits):domain[start].add(word);Q.append((start,word))
while Q:
 q,x=Q.popleft();b=bool(x&center);w,d,z=T[q,b]
 if z not in domain:continue
 xx=(x&~center)|(w<<k)
 if d==1:base=xx>>1;nexts=(base,base|(1<<(2*k)))
 else:base=(xx<<1)&mask;nexts=(base,base|1)
 for y in nexts:
  if y not in domain[z]:domain[z].add(y);Q.append((z,y))
contexts={(q,b):tuple(sorted(x for x in domain[q]if bool(x&center)==b))for q in S for b in(0,1)}
@functools.lru_cache(None)
def outcomes(action,x):
 write,h,q=action;tape=(x&~center)|(write<<k);seen=set();trace=[];out=[];visited=set()
 while True:
  out.append(((q,h,tape),len(trace),frozenset(visited)))
  config=(q,h,tape)
  if abs(h)>k or config in seen or(q,int(bool(tape&(1<<(k+h)))))not in T:break
  seen.add(config);idx=k+h;b=int(bool(tape&(1<<idx)));w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);visited.add(q);tape=(tape&~(1<<idx))|(w<<idx);h+=d;q=z
 return out,trace
@functools.lru_cache(None)
def oldendpoints(q,x):
 oo,_=outcomes(T[q,int(bool(x&center))],x)
 return {config:tick for config,tick,vis in oo}
@functools.lru_cache(None)
def join(q,act,tag):
 olds=oldendpoints(q,tag);oo,_=outcomes(act,tag)
 for cfg,tick,vis in oo:
  if q in vis:break
  if cfg in olds:return olds[cfg],tick,vis
 return None
opts=collections.defaultdict(dict);begin=time.monotonic();actions=list(itertools.product((0,1),(-1,1),S))
for qi,q in enumerate(S):
 for b in(0,1):
  tags=contexts[q,b];target=T[q,b]
  for act in actions:
   vis=set();valid=True
   for tag in tags:
    match=join(q,act,tag)
    if match is None:valid=False;break
    vis.update(match[2])
   if valid:opts[q,b][act]=vis
 if qi%30==0:print('scan',qi,'cached',outcomes.cache_info().currsize,'sec',time.monotonic()-begin,flush=True)
hits=[];tested=0
for keep,drop in itertools.permutations((q for q in S if q!=start),2):
 tested+=1;oo=[]
 for b in(0,1):
  if T[keep,b]==T[drop,b]:options=[T[keep,b]]
  else:options=[act for act in opts[keep,b].keys()&opts[drop,b].keys()if drop not in opts[keep,b][act]and keep not in opts[drop,b][act]]
  oo.append(options)
 if not all(oo):continue
 for aa,bb in itertools.product(*oo):
  U={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in T.items()if q!=drop}
  for b,action in enumerate((aa,bb)):
   w,d,z=action;U[keep,b]=(w,d,keep if z==drop else z)
  stem=f'keep{keep}-drop{drop}-{len(hits)}';(a.output/(stem+'.tm')).write_text(f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items())))
  hit={'keep':keep,'drop':drop,'actions':[aa,bb],'states':len(U)//2,'domains':{str(q):sorted(domain[q])for q in(keep,drop)}}
  traces={}
  for q,b in itertools.product((keep,drop),(0,1)):
   act=(aa,bb)[b]
   if act==T[q,b]:continue
   traces[f'{q},{b}']={}
   for tag in contexts[q,b]:
    _,tr=outcomes(act,tag);oldcount,count,vis=join(q,act,tag);_,oldtr=outcomes(T[q,b],tag)
    traces[f'{q},{b}'][str(tag)]={'old_after_first':oldtr[:oldcount],'new_after_first':tr[:count]}
  hit['traces']=traces;hits.append(hit);print('HIT',stem,aa,bb,flush=True)
res={'table':str(a.table),'table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'radius':k,'domain':{q:sorted(ds)for q,ds in domain.items()},'states':len(S),'pairs':tested,'hits':hits,'seconds':time.monotonic()-begin,'cache':str(outcomes.cache_info()),'scope':'Finite inductive symmetric-window invariant from all initial tapes; exact positive old/new whole-window blocks match complete tape/head/state; new blocks exclude both rewritten states from all helper interiors.'}
(a.output/'result.json').write_text(json.dumps(res,indent=2)+'\n');print('complete','radius',k,'pairs',tested,'hits',len(hits),'seconds',res['seconds'],flush=True)
