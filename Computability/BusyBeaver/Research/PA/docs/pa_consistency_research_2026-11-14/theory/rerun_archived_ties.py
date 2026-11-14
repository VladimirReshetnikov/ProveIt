from pathlib import Path
import sys,json,time
W=Path(__file__).resolve().parent
AX=W/'code'
sys.path[:0]=[str(AX/'search'),str(AX)]
import support as s
c=s.c
INC=('leaf','inc',1)
CLOSES={'cb1':((0,False,302),None),'cd3':((1,True,17),3),'cd4':((1,True,144),4),'cd5':((1,True,45),5),'cd6':((1,True,21),6),'r113':((1,True,113),None),'r103':((1,True,103),6)}
def canonical(t):
 if not c.isnode(t):return t
 a,b=map(canonical,t)
 if (a,b)==(INC,INC):return 'node60'
 if (a,b)==('node60','node60'):return 'node61'
 return (a,b)
def build(t,closing):
 old,labels=c.machine();rows={(q,b):a for(q,b),a in old.items()if q<1300};index={};shape={}
 def state(t):
  if t in c.MACROS:return c.MACROS[t]
  if t in index:return index[t]
  assert c.isnode(t),t
  q=2000+len(index);index[t]=q;shape[q]=t
  for b,ch in enumerate(t):rows[q,b]=closing if ch==c.BREAK else (b,True,state(ch))
  return q
 root=state(t);rows[101,1]=(1,True,root)
 return rows,index,shape

def restore_cpp(d,cfg):
 symbols=[tuple(x)if isinstance(x,list)else x for x in cfg['symbols']]
 memo={}
 def rec(x):
  if x<0:return symbols[-x-1]
  if x not in memo:memo[x]=tuple(rec(y)for y in d['rules'][x])
  return memo[x]
 return rec(d['root'])
def expandedword(t):
 w=s.tree_word(t);v=[]
 for a in w:
  v.extend([INC]*2 if a=='node60'else[INC]*4 if a=='node61'else[a])
 return v

def closing_contracts(t,reg):
 sites,ins,cs=c.source(t)
 p=(1,0,1,0,1,0,0,1);x=t
 while c.isnode(x):p+=(1,);x=x[1]
 assert x==c.BREAK,(x,p)
 close=next(i for i,(path,op,arg)in enumerate(sites)if path==p)
 assert sites[close][1:]==('breakTo',1)
 return [(i,(c.PHYSICAL[reg],True)if i==close and reg is not None else br,st,ta)for i,br,st,ta in cs],close

def main():
 (W/'rerun_output').mkdir(exist_ok=True)
 pool={}
 for p in sorted((W/'experiments/prior_ties').glob('*.json')):
  t=canonical(c.read_grammar(p));pool.setdefault(t,[]).append(str(p.relative_to(W)))
 if '--include-current' in sys.argv:
  cfg=json.loads((W/'experiments/current_search_inputs.json').read_text())
  for p in sorted((W/'experiments').glob('*_gate*.json')):
   d=json.loads(p.read_text())
   t=canonical(restore_cpp(d,cfg));pool.setdefault(t,[]).append(str(p.relative_to(W)))
 rec=[];best={};start=time.time()
 for k,(t,names)in enumerate(pool.items()):
  wl=len(expandedword(t))
  for name,(act,reg)in CLOSES.items():
   rows,ind,shape=build(t,act);ops=c.opportunities_fast(rows,shape);bound=len(c.max_matching(ops))
   count=len(rows)//2-bound
   r={'layout':names,'wordlength':wl,'closing':name,'raw_states':len(rows)//2,'matching_bound':bound,'lower_score':count}
   if name not in best or count<=best[name][0]:
    folds=s.bestcompatible_all(rows,shape);folded,alias=s.apply(rows,folds);count=len(folded)//2
    r.update(compatible_folds=len(folds),working_states=count)
    if name not in best or count<best[name][0]:best[name]=(count,t,folds,r)
    if count<196:
     cs,close=closing_contracts(t,reg);r['contracts']=c.validate(folded,cs);r['closing_source_pc']=close
     out=W/'rerun_output'/f'closing_winner_{name}_{k}.json'
     out.write_text(json.dumps({'grammar':s.encode(t),'folds':folds,'receipt':r},indent=2)+'\n')
     print('WINNER',json.dumps(r),flush=True)
   rec.append(r)
  if(k+1)%10==0:print('progress',k+1,'/',len(pool),'best',{n:v[0]for n,v in best.items()},'seconds',round(time.time()-start,2),flush=True)
 print('counts',len(pool),len(rec),{n:v[0]for n,v in best.items()},flush=True)
 for name,(count,t,folds,r)in best.items():
  act,reg=CLOSES[name];rows,ind,shape=build(t,act);folded,alias=s.apply(rows,folds);cs,close=closing_contracts(t,reg)
  r.update(contracts=c.validate(folded,cs),closing_source_pc=close)
  print('validated',name,json.dumps(r),flush=True)
  (W/'rerun_output'/f'closing_best_{name}.json').write_text(json.dumps({'grammar':s.encode(t),'folds':folds,'receipt':r},indent=2)+'\n')
 (W/'rerun_output/closing_ties_receipt.json').write_text(json.dumps({'layouts':len(pool),'cases':len(rec),'results':rec,'best':{n:v[3]for n,v in best.items()}},indent=2)+'\n')
if __name__=='__main__':main()
