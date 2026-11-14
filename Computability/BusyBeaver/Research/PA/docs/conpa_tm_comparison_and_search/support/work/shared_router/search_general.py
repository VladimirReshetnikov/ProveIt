"""Shared new selector, with existing bounded excursions as providers."""
import sys,json,itertools,collections,time
from pathlib import Path
out=Path(__file__).resolve().parent
SIDE=int(sys.argv[1]) if len(sys.argv)>1 else -1
sys.path.insert(0,str(out.parent/'optimize196'))
from core import *
rows,labels=machine();cs=contracts();RAD=10;LIMIT=24
contexts=collections.defaultdict(set);uses=collections.defaultdict(set)
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
current=0
def observe(s):
    q,onl,l,r=s
    if q not in BOXSTATES and not onl and r and r[0][0]=='b':
        contexts[q,r[0][1]].add(tuple(reversed(take(l,RAD)))+take(r,RAD+1))
        uses[q,r[0][1]].add(current)
for i,c in enumerate(cs):
    current=i;assert run(rows,c,observe=observe) is not None
print('contexts',sum(map(len,contexts.values())),flush=True)

def provider_ok(u,tape,act):
    w,d,n=act;goal=tape[:RAD]+(w,)+tape[RAD+1:];posgoal=RAD+(1 if d else -1)
    t=list(tape);q=u;p=RAD
    for k in range(LIMIT+1):
        if q==n and p==posgoal and tuple(t)==goal:return True
        if p<0 or p>=len(t) or t[p]<0:return False
        z=rows.get((q,t[p]))
        if z is None:return False
        wr,dr,q=z;t[p]=wr;p+=1 if dr else -1
    return False

P={}
for rb,ts in contexts.items():
    poss=set(labels[:-1])
    for t in ts:
        poss={u for u in poss if provider_ok(u,t,rows[rb])}
        if not poss:break
    P[rb]=poss
print('providers computed',sum(map(len,P.values())),flush=True)
(out/'providers.json').write_text(json.dumps({f'{q}/{b}':sorted(v) for (q,b),v in P.items()},indent=2))
ctx={k:{t[RAD+SIDE] for t in ts} for k,ts in contexts.items()}
repl={tuple(map(int,k.split('/'))):[tuple(a) for a in v] for k,v in json.loads((out.parent/'optimize196/action_replacements.json').read_text()).items()}
states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84 and all((q,b) in contexts for b in (0,1))]
groups=collections.defaultdict(list)
for a,b in itertools.combinations(states,2):
    for mask in (1,2,3):
        pp=[set(labels[:-1])-{a,b},set(labels[:-1])-{a,b}];same={};good=True
        for bit in (0,1):
            if mask&(1<<bit):
                ca,cb=ctx[a,bit],ctx[b,bit]
                if ca&cb or -1 in ca or -1 in cb or len(ca)!=1 or len(cb)!=1:
                    good=False;break
                pp[next(iter(ca))]&=P[a,bit]
                pp[next(iter(cb))]&=P[b,bit]
            else:
                common=({rows[a,bit]}|set(repl.get((a,bit),[])))&({rows[b,bit]}|set(repl.get((b,bit),[])))
                common={z for z in common if z[2] not in {a,b}}
                if not common:good=False;break
                same[bit]=sorted(common)
        if not good or not all(pp):continue
        # Initially use the shortest-looking direct common action.
        for u,v in itertools.product(*pp):groups[u,v].append((a,b,mask,same))
print('groups',len(groups),flush=True)
rank=[]
for uv,pairs in groups.items():
    best=[]
    for first in pairs:
        selected=[first];used={first[0],first[1]}
        for p in pairs:
            if not used&{p[0],p[1]}:
                selected.append(p);used|={p[0],p[1]}
        if len(selected)>len(best):best=selected
    if len(best)>1:rank.append((len(best),uv,best))
rank.sort(key=lambda z:z[0],reverse=True)
print('ranked',len(rank),'best',rank[:5],flush=True)
for score,(u,v),pairs in rank:
    # Try pairs before larger sets, which limits dependencies introduced by providers.
    options=[pairs]+list(itertools.combinations(pairs,2))
    for selected in options:
        aliases={a:b for a,b,_,_ in selected};newq=2000
        options=[];keys=[]
        for a,b,mask,same in selected:
            for bit in (0,1):
                keys.append((b,bit));options.append([(bit,SIDE==1,newq)] if mask&(1<<bit) else same[bit])
        affected=sorted(set().union(*(uses[q,c] for a,b,_,_ in selected for q in (a,b) for c in (0,1))))
        for acts in itertools.product(*options):
            rr=dict(zip(keys,acts));new={}
            for (q,c),act in rows.items():
                if q in aliases:continue
                w,d,n=rr.get((q,c),act);new[q,c]=(w,d,aliases.get(n,n))
            new[newq,0]=(0,SIDE==-1,aliases.get(u,u));new[newq,1]=(1,SIDE==-1,aliases.get(v,v))
            ans=validate(new,[cs[i] for i in affected])
            if not ans['ok']:continue
            ans=validate(new,cs)
            print('RESULT',score,u,v,selected,ans,flush=True)
            if ans['ok']:
                artifact={'working_states':len(new)//2,'selector':[u,v],'folds':selected,'rows':[[q,c,w,d,n] for (q,c),(w,d,n) in sorted(new.items())],'validation':ans}
                (out/'candidate_general.json').write_text(json.dumps(artifact,indent=2));raise SystemExit(0)
print('no candidate',flush=True)
