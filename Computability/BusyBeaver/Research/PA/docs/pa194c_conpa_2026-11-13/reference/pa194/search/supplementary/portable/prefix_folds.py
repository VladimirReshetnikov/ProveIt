from pathlib import Path
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]/'construction'
OUT=HERE.parent/'generated'
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT))
import compiler as c
from support import apply,localvalid
c.MACROS[(('leaf','inc',1),('leaf','inc',1))]=99
c.MACROS[((('leaf','inc',1),('leaf','inc',1)),(('leaf','inc',1),('leaf','inc',1)))]=190
rows,ix,shape=c.build(c.read_grammar(ROOT/'inputs/parent195S.grammar.json'))
folds=json.loads((ROOT/'inputs/parent195S.folds.json').read_text());base,alias=apply(rows,folds)
K=int(sys.argv[1]) if len(sys.argv)>1 else 2
used={q for a,b,acts in folds for q in(a,b)}
from functools import lru_cache
from collections import defaultdict
incoming=defaultdict(list)
for (q,v),(w,d,n) in rows.items():incoming[n].append((q,v,w,d))
@lru_cache(None)
def contexts(q,k):
 if not k:return {()}
 out=set()
 for p,v,w,d in incoming[q]:
  if not d:return set(itertools.product((0,1),repeat=k))
  for pref in contexts(p,k-1):out.add(pref+(w,))
 if not out or q==74:return set(itertools.product((0,1),repeat=k))
 return out

checks=0

def trial(a,b,bit,act,ctx,oldq,bound=80):
    w,d,n=rows[oldq,bit]; n=alias.get(n,n);n=b if n==a else n
    expect=list(ctx)+[w]; tape=list(ctx)+[bit]; pos=K;now=b
    for step in range(bound):
        if step and now==n and pos==K+(1 if d else -1) and tape==expect:return step
        if pos<0 or pos>K:return None
        if step and now==b:return None
        if step==0: w2,d2,n2=act
        else:
          action=base.get((now,tape[pos]))
          if action is None:return None
          w2,d2,n2=action
        if n2==a:n2=b
        tape[pos]=w2;pos+=1 if d2 else -1;now=n2
    return None

pairs=[(a,b) for a,b in itertools.combinations(shape,2) if not {a,b}&used and not contexts(a,K)&contexts(b,K)]
print('pairs',len(pairs),'K',K,flush=True)
found=[]
for cnt,(a,b) in enumerate(pairs):
    opts=[]
    for bit in (0,1):
        good=[]
        acts=[rows[a,bit]] if rows[a,bit]==rows[b,bit] else []
        acts += list(itertools.product((0,1),(False,),{q for q,_ in base}-{a,b}))
        for act in acts:
            lens=[]
            for oq in (a,b):
              for ctx in contexts(oq,K):
                l=trial(a,b,bit,act,ctx,oq)
                if l is None:break
                lens.append(l)
              else:continue
              break
            else:good.append((act,lens))
        opts.append(good)
        if not good:break
    if len(opts)==2 and all(opts):
        print('Opportunity',a,b,opts,'contexts',contexts(a,K),contexts(b,K),flush=True)
        for x,y in itertools.product(*opts):
            new=folds+[[a,b,[x[0],y[0]]]]
            out,al=apply(rows,new)
            # All pre-existing local contracts must remain valid. New pair
            # has its own larger-context proof and is not tested by localvalid.
            if localvalid(rows,out,al,folds):
                print('VALIDOLD!',new,flush=True);found.append({'folds':new,'contexts':[list(contexts(a,K)),list(contexts(b,K))]})
    if cnt%100==0:print('progress',cnt,flush=True)
print('complete',len(pairs),len(found),flush=True)
(OUT/f'prefix_folds_k{K}_receipt.json').write_text(json.dumps({'pairs':len(pairs),'k':K,'found':found},indent=2))
