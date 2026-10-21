#!/usr/bin/env python3
"""Extract exact source layouts and measure current physical allocation."""
import argparse,functools,json,sys,time,hashlib,collections,importlib.util
from pathlib import Path
from model import leaf,parse,leaves,graph,arithmetic_graph,localg,nodes
ap=argparse.ArgumentParser();ap.add_argument('--samples',type=Path,required=True);ap.add_argument('--model',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=2000);ap.add_argument('--keep-prefix',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
packet=Path(__file__).resolve().parent.parent;lib=packet/'vendor';sys.path.insert(0,str(lib));import source_language as s;import build221 as b;import measure
m=json.loads(a.model.read_text());P=m['productions'];L={int(q):tuple(n)for q,n in m['leaves'].items()};root=m['root']
oldrows=json.loads((packet/'inputs/sites218.json').read_text());oldsrc=parse(oldrows);oldnodes=set(nodes(oldsrc));T=b.read_table((packet/'inputs/k218.native.tm').read_bytes());oldG=graph(oldrows)
@functools.lru_cache(None)
def rep(q):return L[q]if q in L else (rep(P[q][0][0]),rep(P[q][0][1]))
ids={localg(rep(q)):q for q in range(len(P))};force={}
def anchors(n,start=0):
 if leaf(n)or start>=37:return
 force[ids[localg(n)]]=(ids[localg(n[0])],ids[localg(n[1])]);anchors(n[0],start);anchors(n[1],start+len(leaves(n[0])))
if a.keep_prefix:anchors(oldsrc)
seen=set();records=[];counts=collections.Counter();best=218;started=time.monotonic()
def minimize(table):
 states=sorted({q for q,b in table});part={q:1 for q in states};part[254]=0
 while True:
  signatures={q:tuple((w,d,part[z])for w,d,z in(table[q,0],table[q,1]))for q in states};labels={};new={254:0}
  for q in states:new[q]=labels.setdefault(signatures[q],len(labels)+1)
  if all(new[q]==part[q]for q in states):break
  part=new
 groups=collections.defaultdict(list)
 for q in states:groups[new[q]].append(q)
 mp={q:min(group)for group in groups.values()for q in group};mp[254]=254
 out={}
 for(q,b),(w,d,z)in table.items():
  row=(w,d,mp[z]);key=(mp[q],b)
  if key in out:assert out[key]==row
  out[key]=row
 return out,mp
def extract(selected,mode):
 chosen={q:L[q]for q in L};lead={q:0 for q in L};zero=lead.copy();depth=lead.copy()
 for q,ps in enumerate(P):
  if q in L or q not in selected:continue
  opts=[]
  for x,y in ps:
   if q in force and (x,y)!=force[q]:continue
   if x not in chosen or y not in chosen:continue
   ll=lead[x]+1;zz=max(ll,zero[x],zero[y]);dd=max(depth[x],depth[y])+1
   if zz>6:continue
   nn=(chosen[x],chosen[y]);old=int(nn not in oldnodes)
   score=(old,zz,ll,dd,x,y)if mode==0 else(ll,zz,old,dd,x,y)
   opts.append((score,nn,ll,zz,dd))
  if opts:
   score,nn,ll,zz,dd=min(opts);chosen[q]=nn;lead[q]=ll;zero[q]=zz;depth[q]=dd
 return chosen.get(root)
for ix,line in enumerate(a.samples.read_text().splitlines()[:a.limit]):
 selected=set(map(int,line.split()))|L.keys()
 for mode in(0,1):
  nn=extract(selected,mode)
  if nn is None:counts['no_maxzero6_parse']+=1;continue
  raw=s.compact(s.sites(nn));sha=hashlib.sha256(raw).hexdigest()
  if sha in seen:continue
  seen.add(sha);rows=s.sites(nn)
  assert graph(rows)==oldG==arithmetic_graph(rows)
  if a.keep_prefix:assert rows[:37]==oldrows[:37]
  rec={'index':ix,'mode':mode,'source_sha256':sha,'metrics':s.metrics(nn),'prefix37_equal':rows[:37]==oldrows[:37]}
  try:
   rawtt,info=measure.compile_tree(s,b,T,oldsrc,nn);tt,mp=minimize(rawtt);rec['allocation']=info;states=len(tt)//2;rec['minimized_states']=states;counts[f'states_{states}']+=1
   if states<=218:
    dest=a.output/f'layout_{ix}_{mode}_{states}';dest.mkdir(exist_ok=True);(dest/'sites.json').write_bytes(raw);(dest/'candidate.tm').write_bytes(b.table_bytes(tt));(dest/'metadata.json').write_text(json.dumps(rec,indent=2)+'\n');rec['artifact']=str(dest)
    if tt!=rawtt:(dest/'before_minimization.tm').write_bytes(b.table_bytes(rawtt));(dest/'partition.json').write_text(json.dumps(mp,sort_keys=True)+'\n')
   if states<best:best=states;print('BEST',states,'ix',ix,'mode',mode,rec.get('artifact'),flush=True)
  except Exception as e:rec['error']=repr(e);counts['allocation_error']+=1
  records.append(rec)
 if ix%50==0:print('PROGRESS',ix,'distinct',len(seen),'counts',dict(counts),'seconds',time.monotonic()-started,flush=True)
(a.output/'result.json').write_text(json.dumps({'source_table':str(packet/'inputs/k218.native.tm'),'source':str(packet/'inputs/sites218.json'),'force_prefix37':a.keep_prefix,'distinct':len(seen),'best':best,'counts':counts,'records':records,'seconds':time.monotonic()-started},indent=2)+'\n')
print('DONE',len(seen),'best',best,dict(counts),flush=True)
