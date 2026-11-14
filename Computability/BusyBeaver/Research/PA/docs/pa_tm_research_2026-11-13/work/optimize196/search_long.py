from core import *
from collections import defaultdict
import time

import sys
if len(sys.argv)>1:
    from layout import read_grammar,source
    candidate=json.loads(Path(sys.argv[1]).read_text())
    rows={(q,b):(w,d,n)for q,b,w,d,n in candidate['rows']}
    labels=sorted({q for q,b in rows})+[254]
    cs=source(read_grammar(candidate['source_grammar']))[2]
else:
    rows,labels=machine();cs=contracts()
RAD=12;LIMIT=20
contexts=defaultdict(set);uses=defaultdict(set)
def bits_of(segs,n):
    out=[]
    for x in segs:
        if x[0]=='b':out.append(x[1])
        elif x[0]=='r':
            out += [x[1]] * min(n-len(out),x[3])
            if x[2] and len(out)<n:break
        else:
            out.append(0);break
        if len(out)>=n:break
    return tuple(out[:n])+(-1,)*max(0,n-len(out))

current=None
def observe(s):
    q,onl,l,r=s
    if q not in BOXSTATES and not onl and r and r[0][0]=='b':
        b=r[0][1]
        tape=tuple(reversed(bits_of(l,RAD)))+bits_of(r,RAD+1)
        contexts[q,b].add(tape);uses[q,b].add(current)
for idx,c in enumerate(cs):
    current=idx
    assert run(rows,c,observe=observe) is not None
print('baseline contexts',len(contexts),'unique',sum(map(len,contexts.values())),flush=True)

def reaches(repl,tape,act,steps=LIMIT):
    w,d,n=act
    goal=tape[:RAD]+(w,)+tape[RAD+1:]
    target=RAD+(1 if d else -1)
    wr,dr,h=repl
    t=list(tape);t[RAD]=wr;q=h;p=RAD+(1 if dr else -1)
    for k in range(steps+1):
        if q==n and p==target and tuple(t)==goal:return True
        if p<0 or p>=len(t) or t[p]<0:return False
        a=rows.get((q,t[p]))
        if a is None:return False
        wr,dr,q=a;t[p]=wr;p+=1 if dr else -1
    return False

possible={}
for rb,ts in contexts.items():
    q,b=rb
    if q==84:continue
    hs={(w,d,h) for w in (0,1) for d in (False,True) for h in labels if h!=q}
    for t in ts:
        hs={h for h in hs if reaches(h,t,rows[rb])}
        if not hs:break
    possible[rb]=hs
print('nonempty row replacements',sum(bool(h) for h in possible.values()),flush=True)
Path('action_replacements.json').write_text(json.dumps({f'{q}/{b}':sorted(h) for (q,b),h in possible.items() if h},indent=2))

states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84 and all((q,b) in contexts for b in (0,1))]
candidates=[]
for a,b in itertools.combinations(states,2):
    opts=[]
    for bit in (0,1):
        if rows[a,bit]==rows[b,bit]:opts.append([rows[a,bit]])
        else:opts.append([t for t in (possible[a,bit]&possible[b,bit]) if t[2] not in (a,b)])
    if all(opts):candidates.append((a,b,opts))
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
                Path(f'candidate_{a}_{b}.json').write_text(json.dumps({'remove':a,'retain':b,'replacement_rows':[tr0,tr1],'rows':[[q,bit,*tr] for (q,bit),tr in sorted(new.items())],'validation':ans},indent=2))
                raise SystemExit(0)
