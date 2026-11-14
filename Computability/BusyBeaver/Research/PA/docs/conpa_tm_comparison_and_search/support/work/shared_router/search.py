"""Search simultaneous predecessor-context folds sharing one new selector."""
import sys, json, itertools, collections, time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'optimize196'))
from core import machine, contracts, validate, BOXSTATES

out=Path(__file__).resolve().parent
rows,labels=machine()
contexts={tuple(map(int,k.split('/'))):set(v) for k,v in json.loads((out.parent/'optimize196/contexts.json').read_text()).items()}
states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84 and all((q,b) in contexts for b in (0,1))]
providers=collections.defaultdict(list)
for (q,b),act in rows.items():providers[b,act].append(q)
groups=collections.defaultdict(list)
plausible=0
for a,b in itertools.combinations(states,2):
    differing=[c for c in (0,1) if rows[a,c]!=rows[b,c]]
    if not differing:continue
    requirements=[{},{}]
    good=True
    for c in differing:
        ca,cb=contexts[a,c],contexts[b,c]
        if None in ca or None in cb or ca&cb or len(ca)!=1 or len(cb)!=1:
            good=False;break
        requirements[next(iter(ca))][c]=rows[a,c]
        requirements[next(iter(cb))][c]=rows[b,c]
    if not good:continue
    pp=[]
    for req in requirements:
        ps=set(labels[:-1])-{a,b}
        for c,act in req.items():ps&=set(providers[c,act])
        pp.append(ps)
    if not all(pp):continue
    plausible+=1
    for u,v in itertools.product(*pp):
        groups[u,v].append((a,b,tuple(differing)))
print('plausible pairs',plausible,'selector groups',len(groups),flush=True)
ranked=[]
for (u,v),pairs in groups.items():
    # Compatible folds cannot alter either provider or another fold's state.
    allowed=[p for p in pairs if not ({p[0],p[1]}&{u,v})]
    best=[]
    for first in allowed:
        selected=[first];used={first[0],first[1]}
        for p in allowed:
            if not used&{p[0],p[1]}:
                selected.append(p);used|={p[0],p[1]}
        if len(selected)>len(best):best=selected
    if len(best)>1:ranked.append((len(best),u,v,best))
ranked.sort(reverse=True)
print('groups supporting >=2 disjoint folds',len(ranked),'best',ranked[:10],flush=True)
cs=contracts()
for savings,u,v,pairs in ranked:
    alias={a:b for a,b,_ in pairs}
    newq=2000
    replacements={}
    for a,b,bits in pairs:
        for bit in (0,1):replacements[b,bit]=(bit,False,newq) if bit in bits else rows[b,bit]
    new={}
    for (q,c),act in rows.items():
        if q in alias:continue
        w,d,n=replacements.get((q,c),act)
        new[q,c]=(w,d,alias.get(n,n))
    new[newq,0]=(0,True,u);new[newq,1]=(1,True,v)
    ans=validate(new,cs)
    print('candidate',len(new)//2,u,v,pairs,ans,flush=True)
    if ans['ok']:
        artifact={'working_states':len(new)//2,'selector':[u,v],'folds':pairs,'rows':[[q,c,w,d,n] for (q,c),(w,d,n) in sorted(new.items())],'validation':ans}
        (out/'candidate.json').write_text(json.dumps(artifact,indent=2))
        break
