from fixed_k import *
import random,collections,time
from nonlocal_reassociate import Dag

def trial(a,b,offset,shape,seed,region):
 d=Dag();d.intern(z.TREE)
 mapping={**o.M,'p':pushconst(a,shape),'y':pushconst(b,shape),'C':o.M['c']if offset==0 else(o.M['c'],plus(offset,shape))}
 if region=='k':lo,hi=2650,4563;word=NEWWORD
 else:lo,hi=135,4563;word=sum((o.postfix(f,set())for f in o.FORMULAS[:-1]),[])+NEWWORD
 outside=splice(z.TREE,lo,hi,None);oid=d.intern(outside)
 seq=[d.intern(atom)for tok in word for atom in o.atoms(mapping[tok])]
 avail=d.reach(oid)
 for q in seq:avail.update(d.reach(q))
 rng=random.Random(seed)
 while len(seq)>1:
  counts=collections.Counter(zip(seq,seq[1:]));ranks=[]
  for p,n in counts.items():
   x,y=p
   if 1+d.leading[x]>6:continue
   q=d.index.get(p);cost=0 if q in avail else 1
   score=n-cost+(.05 if q is not None else 0)+rng.random()*.8
   ranks.append((score,p))
  ranks.sort(reverse=True);applied=False
  for _,p in ranks:
   x,y=p;new=[];i=0;used=0
   while i<len(seq):
    allowed=(i!=0 or len(seq)==2)and(i+2==len(seq)or 1+d.leading[x]<6)
    if i+1<len(seq)and(seq[i],seq[i+1])==p and allowed and(i!=0 or 1+d.leading[x]<=(4 if seed%2 else 3)):
     q=d.add(p);new.append(q);used+=1;i+=2
    else:new.append(seq[i]);i+=1
   if used:avail.add(q);seq=new;applied=True;break
  if not applied:return None
 return splice(z.TREE,lo,hi,d.tree(seq[0]))

if __name__=='__main__':
 out=ROOT/'fixed_k_repair_results';out.mkdir(exist_ok=True);start=time.monotonic();results=[]
 for a,b,offset in [(0,1,2),(1,0,2),(1,8,0),(8,1,0)]:
  for region in ['k','ax']:
   best=999;bt=None;hist=collections.Counter()
   for seed in range(100):
    t=trial(a,b,offset,'balanced',seed,region)
    if t is None:continue
    m=z.s.metrics(t);n=m['dag_nodes'];hist[n,m['maximum_zero_run']]+=1
    if m['maximum_zero_run']>6 or m['maximum_depth']>63:continue
    if n<best:
     best=n;bt=t;bs=seed;print('BEST',a,b,offset,region,seed,m,round(time.monotonic()-start,2),flush=True)
   r={'public_binders':[a,b],'private_offset':offset,'region':region,'best_dag':best,'trials':100,'histogram':[[a,b,n]for(a,b),n in sorted(hist.items())]}
   if bt is not None:
    rows=z.s.sites(bt);ref=make(a,b,offset,'balanced','whole');assert z.flat(bt)==z.flat(ref)
    assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)==z.s.graph_intervals(z.s.sites(ref))
    d=out/f'p{a}_y{b}_c{offset}_{region}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows));r['seed']=bs;r['metrics']=z.s.metrics(bt)
    try:tt,mm=z.compile_tree(z.T,z.TREE,bt);r['compiler']=mm;(d/'candidate.tm').write_bytes(z.b.table_bytes(tt))
    except Exception as e:r['error']=repr(e)
   results.append(r);(out/'summary.json').write_text(json.dumps(results,indent=2)+'\n');print('DONE',r,flush=True)
