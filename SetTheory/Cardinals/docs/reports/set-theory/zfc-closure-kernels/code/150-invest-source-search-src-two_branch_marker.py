#!/usr/bin/env python3
"""Synthesize both decoder branches from exact two-cell helper contracts.

This family allows unequal read-zero and unequal read-one branches. Every
accepted helper restores the two known cells and has identical old endpoint;
all external cells are untouched. States modified/deleted may not appear
inside the reused helper paths. Thus the certificate gives all-tape block
simulation when incoming transitions write the distinguishing marker.
"""
import argparse,json,collections,itertools,time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
T={};start=None
for line in a.table.read_text().splitlines():
 if line.startswith('#! start '):start=int(line[9:]);continue
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
S=sorted({q for q,b in T});incoming=collections.defaultdict(list)
for k,v in T.items():incoming[v[2]].append((k,v))
G={}
for q in S:
 if q==start or not all(T[q,b][:2]==(b,1)for b in(0,1)):continue
 vals={w for k,(w,d,z)in incoming[q]};dirs={d for k,(w,d,z)in incoming[q]}
 if len(vals)==1 and dirs=={1}:G[q]=next(iter(vals))
def outcome(helper,write,bit,marker):
 tape={-1:marker,0:write};q=helper;h=-1;seen=set();trace=[]
 while h!=1:
  config=(q,h,tape[-1],tape[0])
  if h not in tape or config in seen or (q,tape[h])not in T:return None
  seen.add(config);b=tape[h];w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
 if tape!={-1:marker,0:bit}:return None
 return q,trace
catalog=[collections.defaultdict(list)for _ in(0,1)]
for b,w,h in itertools.product((0,1),(0,1),S):
 aa=outcome(h,w,b,0);bb=outcome(h,w,b,1)
 if aa is not None and bb is not None:catalog[b][aa[0],bb[0]].append({'action':[w,-1,h],'traces':[aa[1],bb[1]],'inside':sorted({row[0]for trace in (aa[1],bb[1])for row in trace})})
hits=[];pairs=0
for keep,drop in itertools.permutations(G,2):
 if G[keep]==G[drop]:continue
 pairs+=1;opts=[]
 for b in(0,1):
  tk,td=T[keep,b][2],T[drop,b][2]
  if tk==td:op=[{'action':list(T[keep,b]),'traces':[],'inside':[]}]
  else:
   targets=(tk,td)if G[keep]==0 else(td,tk)
   op=[x for x in catalog[b].get(targets,[])if keep not in x['inside']and drop not in x['inside']]
  opts.append(op)
 if not all(opts):continue
 for o0,o1 in itertools.product(*opts):
  U={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in T.items()if q!=drop}
  for b,o in enumerate((o0,o1)):
   w,d,z=o['action'];U[keep,b]=(w,d,keep if z==drop else z)
  name=f'keep{keep}-drop{drop}-{len(hits)}';data={'keep':keep,'drop':drop,'marker_keep':G[keep],'marker_drop':G[drop],'branch_contracts':[o0,o1],'states':len(U)//2,'incoming_keep':incoming[keep],'incoming_drop':incoming[drop]}
  (a.output/(name+'.tm')).write_text(f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items())))
  hits.append(data);print('HIT',name,'actions',U[keep,0],U[keep,1],flush=True)
res={'source':str(a.table),'family':'both actions via exact arbitrary exterior two-cell contracts; exclude changed states from helper interiors','eligible':G,'pairs':pairs,'catalog_pairs':[len(x)for x in catalog],'catalog_actions':[sum(map(len,x.values()))for x in catalog],'hits':hits}
(a.output/'result.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items()if k not in('hits','eligible')}),'hits',len(hits),flush=True)
