"""Eliminate a control by compressing all incoming odd-length excursions."""
import sys,json,itertools,collections
from pathlib import Path
out=Path(__file__).resolve().parent
sys.path.insert(0,str(out.parent/'optimize196'))
from core import *
rows,labels=machine();cs=contracts();RAD=16;LIMIT=45
contexts=collections.defaultdict(set);uses=collections.defaultdict(set);current=0
def take(segs,n):
    a=[]
    for s in segs:
        if s[0]=='b':a.append(s[1])
        elif s[0]=='r':
            a.extend([s[1]]*min(n-len(a),s[3]))
            if s[2] and len(a)<n:break
        else:a.append(0);break
        if len(a)>=n:break
    return tuple(a[:n])+(-1,)*max(0,n-len(a))
def observe(s):
    q,onl,l,r=s
    if q not in BOXSTATES and not onl and r and r[0][0]=='b':
        contexts[q,r[0][1]].add(tuple(reversed(take(l,RAD)))+take(r,RAD+1))
        uses[q,r[0][1]].add(current)
for i,c in enumerate(cs):
    current=i;assert run(rows,c,observe=observe) is not None
print('contexts',sum(map(len,contexts.values())),flush=True)

def summaries(q,tape):
    t=list(tape);p=RAD;res=set()
    for k in range(LIMIT):
        if p<0 or p>=len(t) or t[p]<0:break
        a=rows.get((q,t[p]))
        if a is None:break
        w,d,q=a;t[p]=w;p+=1 if d else -1
        if abs(p-RAD)==1 and t[:RAD]==list(tape[:RAD]) and t[RAD+1:]==list(tape[RAD+1:]):
            res.add((t[RAD],p>RAD,q))
    return res
opts={}
for (q,b),ts in contexts.items():
    possible=None
    for t in ts:
        cand=summaries(q,t)
        possible=cand if possible is None else possible&cand
        if len(possible)<=1:break
    opts[q,b]=possible
(out/'inline_options.json').write_text(json.dumps({f'{q}/{b}':sorted(v) for (q,b),v in opts.items()},indent=2))
print('nontrivial options',sum(len(v)>1 for v in opts.values()),flush=True)
rank=[]
for deleted in labels[:-1]:
    if deleted in BOXSTATES or deleted==84:continue
    incoming=[k for k,a in rows.items() if a[2]==deleted and k[0]!=deleted]
    poss=[];good=True
    for k in incoming:
        op=[a for a in opts.get(k,[]) if a[2]!=deleted]
        if not op:good=False;break
        poss.append(op)
    if good and incoming:rank.append((deleted,incoming,poss))
print('deletable candidates',[(d,ks,list(map(len,ps))) for d,ks,ps in rank],flush=True)
for d,keys,ps in rank:
    for aa in itertools.product(*ps):
        changes=dict(zip(keys,aa))
        new={k:changes.get(k,a) for k,a in rows.items() if k[0]!=d}
        affected=sorted(set().union(*(uses.get(k,set()) for k in keys)))
        ans=validate(new,[cs[i] for i in affected])
        if ans['ok']:
            ans=validate(new,cs)
            print('RESULT',d,changes,ans,flush=True)
            if ans['ok']:
                artifact={'working_states':len(new)//2,'deleted':d,'rewrites':[[q,c,*z] for (q,c),z in changes.items()],'rows':[[q,c,w,dr,n] for (q,c),(w,dr,n) in sorted(new.items())],'validation':ans}
                (out/'candidate_inline.json').write_text(json.dumps(artifact,indent=2));raise SystemExit(0)
print('no candidate',flush=True)
