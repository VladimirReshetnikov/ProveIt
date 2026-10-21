#!/usr/bin/env python3
"""General-state two-branch fold using finite left-window action contracts."""
import argparse,json,collections,itertools,time,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--radius',type=int,default=5);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
T={};start=None
for line in a.table.read_text().splitlines():
 if line.startswith('#! start '):start=int(line[9:]);continue
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
S=sorted({q for q,b in T});k=a.radius;bits=k+1;mask=(1<<bits)-1;domain={q:set()for q in S};Q=collections.deque()
for word in range(1<<bits):domain[start].add(word);Q.append((start,word))
while Q:
 q,x=Q.popleft();b=x&1;w,d,z=T[q,b]
 if z not in domain:continue
 if d==1:
  xx=((x&~1)|w)<<1;nexts=(xx&mask,(xx|1)&mask)
 else:
  xx=x>>1;nexts=(xx,xx|(1<<k))
 for y in nexts:
  if y not in domain[z]:domain[z].add(y);Q.append((z,y))
contexts={(q,b):{x>>1 for x in domain[q]if x&1==b}for q in S for b in(0,1)}
def outcomes(helper,write,tag):
 tape=(tag<<1)|write;q=helper;h=-1;seen=set();trace=[];out={};visited=set()
 while True:
  if h in(-1,1) and tape>>1==tag:
   endpoint=(tape&1,h,q)
   if endpoint not in out:out[endpoint]=(len(trace),visited.copy())
  config=(q,h,tape)
  if h< -k or h>0 or config in seen or(q,(tape>>(-h))&1)not in T:break
  seen.add(config);b=(tape>>(-h))&1;w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);visited.add(q);tape=(tape&~(1<<(-h)))|(w<<(-h));h+=d;q=z
 return out,trace
catalog={};opts=collections.defaultdict(dict);begin=time.monotonic()
for w,H in itertools.product((0,1),S):
 action=(w,-1,H);outs={tag:outcomes(H,w,tag)for tag in range(1<<k)};catalog[action]=outs
 for q,b in itertools.product(S,(0,1)):
  tags=contexts[q,b];target=T[q,b]
  if tags and all(target in outs[tag][0]for tag in tags):
   visited=set().union(*(outs[tag][0][target][1]for tag in tags))
   if q not in visited:opts[q,b][action]=visited
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
    outs,tr=catalog[act][tag];count,vis=outs[T[q,b]];traces[f'{q},{b}'][str(tag)]=tr[:count]
  hit['traces']=traces;hits.append(hit);print('HIT',stem,aa,bb,flush=True)
res={'table':str(a.table),'table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'radius':k,'domain':{q:sorted(ds)for q,ds in domain.items()},'states':len(S),'pairs':tested,'hits':hits,'seconds':time.monotonic()-begin,'scope':'Finite inductive predecessor-word invariant from all initial tapes; exact whole-window two-action contracts exclude both rewritten states from all helper interiors. Candidate branches may implement any old one-step tape write, direction and target.'}
(a.output/'result.json').write_text(json.dumps(res,indent=2)+'\n');print('complete','radius',k,'pairs',tested,'hits',len(hits),'seconds',res['seconds'],flush=True)
