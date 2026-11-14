from pathlib import Path
from collections import defaultdict,Counter
import itertools,json,time,sys
import build_composites as bc
from support import bestcompatible_all,apply,localvalid,encode
c=bc.c
(bc.ROOT/'search/results').mkdir(parents=True,exist_ok=True)

def helpers(rows,shape):
 incoming=defaultdict(set)
 for(q,b),(w,d,n)in rows.items():
  if d and w==b and n in shape:incoming[n].add(b)
 left=[q for q in shape if incoming[q]=={0}];right=[q for q in shape if incoming[q]=={1}]
 byact=[defaultdict(set),defaultdict(set)]
 for(q,b),a in rows.items():byact[b][a].add(q)
 possible=defaultdict(set)
 for a in left:
  for b in right:
   diff=[v for v in(0,1)if rows[a,v]!=rows[b,v]]
   if len(diff)!=1:continue
   v=diff[0]
   for u0 in byact[v][rows[a,v]]-{a,b}:
    for u1 in byact[v][rows[b,v]]-{a,b}:
     possible[u0,u1].add((a,b,v))
 return possible

if __name__=='__main__':
 start=time.time();paths=[bc.AX/'diagonal196/grammar.json',bc.AX/'separate196/grammar.json']+sorted((bc.AX/'search/ties').glob('*.grammar.json'))
 done=[];best=999;seen=set();newqs=5000
 for p in paths:
  t=c.read_grammar(p)
  if t in seen:continue
  seen.add(t);rows,idx,shape=c.build(t);cand=helpers(rows,shape);hist=Counter();promising=0;record=[]
  for (u0,u1),edges in cand.items():
   if len(edges)<2:continue
   rr=dict(rows);rr[newqs,0]=(0,True,u0);rr[newqs,1]=(1,True,u1)
   ops=c.opportunities_fast(rr,shape);lower=len(rr)//2-len(c.max_matching(ops));hist[lower]+=1
   if lower>=196:continue
   promising+=1;ch=bestcompatible_all(rr,shape);folded,alias=apply(rr,ch);n=len(folded)//2
   record.append({'helper':[u0,u1],'potential_edges':len(edges),'lower':lower,'states':n,'folds':len(ch)})
   if n<best:best=n;print('BEST',p.name,n,'helper',u0,u1,'raw',len(rr)//2,'folds',len(ch),flush=True)
   if n<196:
    ss,ins,cs=c.source(t);val=c.validate(folded,cs);st=bc.startup(folded,ss[25][0]);print('CANDIDATE',n,val,st,flush=True)
    out=bc.ROOT/'search/results'/('synth'+str(n)+'_'+str(len(done))+'_'+str(u0)+'_'+str(u1));out.mkdir(parents=True,exist_ok=True)
    (out/'machine.native.tm').write_text(bc.table_text(folded));(out/'grammar.json').write_text(json.dumps(encode(t),indent=2));(out/'folds.json').write_text(json.dumps(ch,indent=2));(out/'sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a]for p,op,a in ss]));(out/'receipt.json').write_text(json.dumps({'family':str(p),'helper':[u0,u1],'states':n,'validation':val,'startup':st},indent=2))
    if val['ok']and st:sys.exit(0)
  rec={'name':str(p),'helper_options':len(cand),'multiple_options':sum(len(e)>1 for e in cand.values()),'lower_bound_histogram':dict(hist),'promising':promising,'records':record};done.append(rec)
  print(p.name,len(cand),dict(hist),'promising',promising,flush=True)
 (bc.ROOT/'search/results/synth_helper_receipt.json').write_text(json.dumps({'results':done,'seconds':time.time()-start},indent=2)+'\n')
