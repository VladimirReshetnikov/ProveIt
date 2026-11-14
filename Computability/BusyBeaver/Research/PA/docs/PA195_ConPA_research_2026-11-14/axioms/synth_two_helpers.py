from pathlib import Path
from collections import defaultdict,Counter
import itertools,json,time,sys,argparse
import build_composites as bc
from support import bestcompatible_all,apply,localvalid,encode
c=bc.c
(bc.ROOT/'search/results').mkdir(parents=True,exist_ok=True)

def data(rows,shape):
 incoming=defaultdict(set)
 for(q,b),(w,d,n)in rows.items():
  if d and w==b and n in shape:incoming[n].add(b)
 left=[q for q in shape if incoming[q]=={0}];right=[q for q in shape if incoming[q]=={1}]
 byact=[defaultdict(set),defaultdict(set)]
 for(q,b),a in rows.items():byact[b][a].add(q)
 oldops=c.opportunities_fast(rows,shape)
 olds={(a,b)for a,b,_ in oldops}
 providers=[defaultdict(set),defaultdict(set)]
 for h in{q for q,b in rows}:
  w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
  if w0==0 and w1==1 and d0 and d1:
   for v in(0,1):
    if (u0,v)in rows and(u1,v)in rows:providers[v][rows[u0,v],rows[u1,v]].add((h,u0,u1))
 pairs=list(itertools.product(left,right));base={};covers=defaultdict(dict)
 for a,b in pairs:
  mask=0
  for v in(0,1):
   good=rows[a,v]==rows[b,v]or any(not({a,b}&{h,u0,u1})for h,u0,u1 in providers[v].get((rows[a,v],rows[b,v]),()))
   if good:mask|=1<<v
   for u0 in byact[v][rows[a,v]]-{a,b}:
    for u1 in byact[v][rows[b,v]]-{a,b}:
     if not good:covers[u0,u1][a,b]=covers[u0,u1].get((a,b),0)|(1<<v)
  base[a,b]=mask
 return base,covers

def matching(edges):
 ed=defaultdict(list)
 for a,b in edges:ed[a].append(b)
 match={}
 def aug(a,seen):
  for b in ed[a]:
   if b in seen:continue
   seen.add(b)
   if b not in match or aug(match[b],seen):match[b]=a;return True
  return False
 for a in ed:aug(a,set())
 return len(match)

def screen(p,t,out):
 rows,idx,shape=c.build(t);base,covers=data(rows,shape);old={x for x,m in base.items()if m==3}
 # Missing-mask accounting removes pairs that neither helper can complete.
 single={h:{x for x,m in cs.items()if(base[x]|m)==3}for h,cs in covers.items()}
 pool=list(covers);required=len(rows)//2+2-195
 # Any matching has at most old matching + total new edge count.
 m0=matching(old);valid=0;optim=Counter();records=[];best=999;count=0
 for i,h0 in enumerate(pool):
  for h1 in pool[i+1:]:
   count+=1;edges=single[h0]|single[h1]
   for x,m in covers[h0].items():
    if base[x]|m|covers[h1].get(x,0)==3:edges.add(x)
   if len(edges)+m0<required:continue
   k=matching(old|edges);optim[len(rows)//2+2-k]+=1
   if k<required:continue
   valid+=1;rr=dict(rows);rr[5000,0]=(0,True,h0[0]);rr[5000,1]=(1,True,h0[1]);rr[5001,0]=(0,True,h1[0]);rr[5001,1]=(1,True,h1[1])
   ch=bestcompatible_all(rr,shape);folded,alias=apply(rr,ch);n=len(folded)//2
   records.append({'h0':h0,'h1':h1,'lower':len(rows)//2+2-k,'states':n})
   if n<best:best=n;print('LOWER',p.name,'states',n,'h',h0,h1,'folds',len(ch),flush=True)
   if n<196:
    ss,ins,cs=c.source(t);val=c.validate(folded,cs);st=bc.startup(folded,ss[25][0]);print('CANDIDATE',n,val,st,flush=True)
    dest=out/('candidate'+str(n)+'_'+str(valid));dest.mkdir(parents=True,exist_ok=True)
    (dest/'machine.native.tm').write_text(bc.table_text(folded));(dest/'grammar.json').write_text(json.dumps(encode(t),indent=2));(dest/'folds.json').write_text(json.dumps(ch,indent=2));(dest/'sites.json').write_text(json.dumps([[''.join(map(str,p)),o,a]for p,o,a in ss]));(dest/'receipt.json').write_text(json.dumps({'validation':val,'startup':st,'h0':h0,'h1':h1},indent=2))
    if val['ok']and st:return True
 rec={'path':str(p.relative_to(bc.ROOT)),'raw_states':len(rows)//2,'helpers':len(pool),'pairs':count,'surviving_cardinality_filter':sum(optim.values()),'lower_counts':dict(optim),'optimistic195':valid,'records':records}
 (out/(p.parent.name+'_'+p.stem+'.json')).write_text(json.dumps(rec,indent=2)+'\n');print('DONE',p.name,len(pool),count,dict(optim),valid,flush=True)
 return False
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--all',action='store_true');a=ap.parse_args();out=bc.ROOT/'search/results/two_helpers';out.mkdir(parents=True,exist_ok=True)
 paths=[bc.AX/'diagonal196/grammar.json',bc.AX/'separate196/grammar.json']+sorted((bc.AX/'search/ties').glob('*.grammar.json'))
 if not a.all:paths=paths[:2]+paths[::10]
 seen=set()
 for p in paths:
  t=c.read_grammar(p)
  if t in seen:continue
  seen.add(t)
  if screen(p,t,out):break
