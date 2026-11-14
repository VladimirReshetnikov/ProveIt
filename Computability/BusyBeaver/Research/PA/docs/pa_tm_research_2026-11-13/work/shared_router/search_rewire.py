"""Fold states after freeing selector rows by context-valid rewrites."""
import sys,json,itertools,collections
from pathlib import Path
out=Path(__file__).resolve().parent
sys.path.insert(0,str(out.parent/'optimize196'))
from core import *
rows,labels=machine();cs=contracts()
ctx={tuple(map(int,k.split('/'))):set(v) for k,v in json.loads((out.parent/'optimize196/contexts.json').read_text()).items()}
P={tuple(map(int,k.split('/'))):set(v) for k,v in json.loads((out/'providers.json').read_text()).items()}
alt={tuple(map(int,k.split('/'))):set(map(tuple,v)) for k,v in json.loads((out.parent/'optimize196/action_replacements.json').read_text()).items()}
for key,act in rows.items():alt.setdefault(key,set()).add(act)
states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84 and all((q,b) in P for b in (0,1))]
selectors=[h for h in labels[:-1] if h not in BOXSTATES]
uses=collections.defaultdict(set);current=0
def observe(s):
    q,onl,l,r=s
    if not onl and r:
        b=headbit(r)
        if b is not None:uses[q,b].add(current)
for i,c in enumerate(cs):
    current=i;assert run(rows,c,observe=observe) is not None

def options(a,b,bit):
    out=[]
    common=alt[a,bit]&alt[b,bit]
    for act in common:
        if act[2] not in {a,b}:out.append((act,{}))
    ca,cb=ctx[a,bit],ctx[b,bit]
    if None in ca or None in cb or ca&cb or len(ca)!=1 or len(cb)!=1:return out
    goals={next(iter(ca)):P[a,bit]-{a,b},next(iter(cb)):P[b,bit]-{a,b}}
    for h in selectors:
        if h in {a,b}:continue
        aa=[]
        for p in (0,1):
            aa.append([z for z in alt[h,p] if z[0]==p and z[1] and z[2] in goals[p]])
        for h0,h1 in itertools.product(*aa):
            changes={k:z for k,z in [((h,0),h0),((h,1),h1)] if rows[k]!=z}
            out.append(((bit,False,h),changes))
    return out

candidates=[]
for a,b in itertools.combinations(states,2):
    opts=[options(a,b,bit) for bit in (0,1)]
    for x,y in itertools.product(*opts):
        if not (x[1] or y[1]):continue
        mods=dict(x[1]);good=True
        for k,v in y[1].items():
            if k in mods and mods[k]!=v:good=False;break
            mods[k]=v
        if good:candidates.append((len(mods),a,b,x[0],y[0],mods))
candidates.sort(key=lambda z:z[:3])
print('rewired pair candidates',len(candidates),flush=True)
for trial,(_,a,b,x,y,mods) in enumerate(candidates):
    rr=mods|{(b,0):x,(b,1):y};new={}
    for (q,c),act in rows.items():
        if q==a:continue
        w,d,n=rr.get((q,c),act);new[q,c]=(w,d,b if n==a else n)
    affected=sorted(set().union(*(uses[q,c] for q in (a,b) for c in (0,1))))
    ans=validate(new,[cs[i] for i in affected])
    if ans['ok']:
        ans=validate(new,cs)
        print('RESULT',trial,a,b,x,y,mods,ans,flush=True)
        if ans['ok']:
            artifact={'working_states':len(new)//2,'remove':a,'retain':b,'replacement_rows':[x,y],'rewrites':[[q,c,*z] for (q,c),z in mods.items()],'rows':[[q,c,w,d,n] for (q,c),(w,d,n) in sorted(new.items())],'validation':ans}
            (out/'candidate_rewire.json').write_text(json.dumps(artifact,indent=2));break
    if trial%100==0:print('tried',trial,flush=True)
else:print('no candidate',flush=True)
