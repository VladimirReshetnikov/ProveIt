#!/usr/bin/env python3
"""Independent label permutations inside the unconditional fused heads."""
from pathlib import Path
exec(Path(__file__).with_name('fuse_h2.py').read_text().split("joint='joint'")[0])
for j in range(12):intern(read_grammar(BASE/'work/optimize196'/f'transport_candidates_local_{j}.json'))
byfirst.clear()
for q,w in enumerate(words):byfirst[w[0]].append(q)
OUT=Path(__file__).resolve().parent/'fusion_roles';OUT.mkdir(exist_ok=True)
cs=json.loads((OUT.parent/'fused_unconditional/candidates.json').read_text())
perms=list(itertools.permutations('DHA'))
def rename(t,p):
    if isinstance(t,str):return p['DHA'.index(t)] if t in 'DHA' else t
    k,a,b=t;return(k,rename(a,p),rename(b,p))
best=999;found=[];hist=collections.Counter();count=0;start=time.time()
for j,c in enumerate(cs):
    meta=c['meta'];inner=meta['inner'];outer=meta['outer']
    if len(inner)!=1:continue
    for pp in itertools.product(perms,repeat=2):
        hs=v.heads(meta['flags'],meta['eqflip'],False)
        hs[4]=rename(hs[4],pp[1]);hs[inner[0]]=rename(hs[inner[0]],pp[0])
        body=hs[4][1]
        for k in reversed(inner):body=v.I(hs[k],body)
        hs[4]=v.N(body)
        word=prefix+sum((v.emit(hs[k]) for k in outer),[])+v.emit(v.gate(meta['gate_swap'],meta['eqflip'],False))+suffix
        score,p=parse(word,32);hist[score]+=1;count+=1
        m=dict(meta,roles=pp,original=j)
        if score<best:best=score;print('BEST',best,m,'n',count,'sec',time.time()-start,flush=True)
        if score<=69:
            found.append({'cost':score,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':m,'word':word})
    if j%10==0:print('PROGRESS',j,'best',best,'found',len(found),'sec',time.time()-start,flush=True)
    (OUT/'candidates.json').write_text(json.dumps(found))
(OUT/'receipt.json').write_text(json.dumps({'count':count,'histogram':hist,'best':best,'found':len(found),'seconds':time.time()-start}))
