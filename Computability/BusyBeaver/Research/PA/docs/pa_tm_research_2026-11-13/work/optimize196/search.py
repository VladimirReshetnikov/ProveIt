from core import *
from collections import defaultdict
import time

rows,labels=machine();cs=contracts()
contexts=defaultdict(set);uses=defaultdict(set)
current_contract=None
def observe(s):
    q,onl,l,r=s
    if not onl and r:
        b=headbit(r);prev=headbit(l)
        if b is not None:
            contexts[q,b].add(prev)
            uses[q,b].add(current_contract)

for idx,c in enumerate(cs):
    current_contract=idx
    assert run(rows,c,observe=observe) is not None
print('baseline',len(cs),'rows',len(contexts),flush=True)
Path('contexts.json').write_text(json.dumps({f'{q}/{b}':list(v) for (q,b),v in contexts.items()},indent=2))

def choices(a,b,bit):
    aa=rows[a,bit];bb=rows[b,bit]
    if aa==bb:return [aa]
    ac=contexts[a,bit];bc=contexts[b,bit]
    if None in ac or None in bc or ac & bc:return []
    ret=[]
    for h in labels[:-1]:
        if h in (a,b):continue
        good=True
        for src,ctx in [(a,ac),(b,bc)]:
            for p in ctx:
                w,d,u=rows[h,p]
                if w!=p or not d or u in (a,b) or rows.get((u,bit))!=rows[src,bit]:
                    good=False;break
            if not good:break
        if good:ret.append((bit,False,h))
    return ret

candidates=[]
states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84]
for a,b in itertools.combinations(states,2):
    opts=[choices(a,b,bit) for bit in (0,1)]
    if all(opts):
        candidates.append((a,b,opts))
print('pair candidates',len(candidates),flush=True)
for a,b,opts in candidates:
    print('candidate',a,b,opts,flush=True)
    for tr0,tr1 in itertools.product(*opts):
        new={}
        for (q,bit),(w,d,n) in rows.items():
            if q==a:continue
            if q==b:w,d,n=(tr0,tr1)[bit]
            new[q,bit]=(w,d,b if n==a else n)
        affected=sorted(set.union(*[uses[a,bit] | uses[b,bit] for bit in (0,1)]))
        ans=validate(new,[cs[i] for i in affected])
        if ans['ok']:
            ans=validate(new,cs)
            print('RESULT',a,b,tr0,tr1,ans,flush=True)
            if ans['ok']:
                Path(f'candidate_{a}_{b}.json').write_text(json.dumps({'remove':a,'retain':b,'rows':[[q,bit,*tr] for (q,bit),tr in sorted(new.items())],'validation':ans},indent=2))
                raise SystemExit(0)
