"""Bounded safe-macro reassociation search; no lower-bound claim."""
from pathlib import Path
import sys,json,random,math,time,hashlib
import build_composites as bc
from support import attrs,nodes,bad,rotations,repl,bestcompatible_all,apply,localvalid,encode
c=bc.c
(bc.ROOT/'search/results').mkdir(parents=True,exist_ok=True)
raw=c.raw_nodes()
split={'node65':('node17','node64'),'node49':('node37','node48'),
       'node58':('node49','node57'),'node55':('node49','node54'),
       'node70':('node49','node69')}
extra={'node17':105,'node48':29,'node57':20,'node54':114,
       'node69':179,'node37':28,'node64':106}
def expose(t):
    if isinstance(t,str) and t in split:return tuple(expose(x)for x in split[t])
    return tuple(expose(x)for x in t)if c.isnode(t)else t
for key,val in list(c.MACROS.items()):
    c.MACROS[expose(key)]=val
c.MACROS.update(extra)
out=bc.ROOT/'search/results/split_original';out.mkdir(parents=True,exist_ok=True)
rng=random.Random(2026111305)
def cost(t):
    h,l,m,mi,_=attrs(t);rows,_,shape=c.build(t)
    optimistic=len(c.max_matching(c.opportunities_fast(rows,shape)))
    pen=4*bad(t)+4*max(m-6,0)+4*max(mi-5,0)+max(h-38,0)
    folds=optimistic
    if len(shape)-folds+pen<=63:folds=len(bestcompatible_all(rows,shape))
    eff=len(shape)-folds
    return eff+pen,eff,len(shape),folds,pen,tuple(nodes(t))
paths=[bc.AX/'separate196/grammar.json']+list(sorted((bc.AX/'search/ties').glob('*.grammar.json')))
pool=[];seen=set()
for p in paths:
    t=expose(c.read_grammar(p))
    if t in seen:continue
    seen.add(t);s=cost(t);pool.append((t,s))
pool.sort(key=lambda x:x[1][0]);pool=pool[:50]
best=pool[0][1][0];bestt,bests=pool[0]
start=time.time();attempts=accepted=0
limit=int(sys.argv[1])if len(sys.argv)>1 else 300
print('INITIAL',[(s[:5])for t,s in pool[:5]],flush=True)
def save(t,s):
    (out/'best.grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
    (out/'best.score.json').write_text(json.dumps({'objective':s[0],'effective':s[1],'nodes':s[2],'folds':s[3],'penalty':s[4],'attempts':attempts,'accepted':accepted,'seconds':time.time()-start,'seed':2026111305},indent=2)+'\n')
save(bestt,bests)
while time.time()-start<limit:
    t,s=rng.choice(pool)
    for j in range(1500):
        attempts+=1;x=rng.choice(s[5]);rr=list(rotations(x))
        if not rr:continue
        nt=repl(t,x,rng.choice(rr));ns=cost(nt);temp=.06+.7*(1-j/1500)
        if ns[0]<=s[0]or rng.random()<math.exp(min(0,(s[0]-ns[0])/temp)):
            t,s=nt,ns;accepted+=1
            if s[0]<best:
                best,bestt,bests=s[0],t,s;save(t,s)
                print('BEST',s[:5],attempts,round(time.time()-start,2),flush=True)
            if s[0]<=best and t not in seen and s[4]==0:
                seen.add(t);pool.append((t,s));pool=pool[-100:]
            if s[1]<=61 and s[4]==0:
                rows,_,shape=c.build(t);ch=bestcompatible_all(rows,shape)
                folded,alias=apply(rows,ch);sites,ins,cs=c.source(t)
                # Regrouping must preserve the primitive sequence and CFG exactly.
                _,baseline,_=c.source(c.read_grammar(bc.AX/'separate196/grammar.json'))
                assert ins==baseline,'source CFG changed'
                val=c.validate(folded,cs);st=bc.startup(folded,sites[25][0])
                print('CANDIDATE',len(folded)//2,val,st,flush=True)
                (out/'candidate.native.tm').write_text(bc.table_text(folded))
                (out/'candidate.folds.json').write_text(json.dumps(ch,indent=2)+'\n')
                (out/'candidate.sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a]for p,op,a in sites])+'\n')
                (out/'candidate.receipt.json').write_text(json.dumps({'states':len(folded)//2,'validation':val,'startup_steps':st},indent=2)+'\n')
                if val['ok']and st:
                    save(t,s);raise SystemExit
        if time.time()-start>=limit:break
save(bestt,bests)
print('FINISH',bests[:5],attempts,round(time.time()-start,2),flush=True)
