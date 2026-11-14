#!/usr/bin/env python3
"""Fuse positive heads into the unconditional negative equality-existence head.

The ex-falso bootstrap head remains unchanged.  Thus classical conjunction
introduction/projections prove exact equivalence for every parameter triple.
"""
from pathlib import Path
exec(Path(__file__).with_name('fuse_h2.py').read_text().split("joint='joint'")[0])
OUT=Path(__file__).resolve().parent/'fused_unconditional';OUT.mkdir(exist_ok=True)
best=999;hist=collections.Counter();found=[];start=time.time();count=0
families=[]
for k in range(1,5):
    for selected in itertools.combinations((1,2,3,5),k):
        remaining=[j for j in range(6) if j not in selected]
        for inner in itertools.permutations(selected):
            for outer in itertools.permutations(remaining):
                families.append((inner,outer))
random.Random(13519).shuffle(families)
for inner,outer in families:
  for ef,swap,flags in itertools.product([False,True],[False,True],range(8)):
    hs=v.heads(flags,ef,False)
    # h5 = not(U(D,not(E(H,D)))): append the positive heads inside its negation.
    body=hs[4][1]
    for j in reversed(inner):body=v.I(hs[j],body)
    hs[4]=v.N(body)
    word=prefix+sum((v.emit(hs[j]) for j in outer),[])+v.emit(v.gate(swap,ef,False))+suffix
    assert len(word)==201+len(inner)
    score,p=parse(word,8);hist[score]+=1;count+=1
    meta={'inner':inner,'outer':outer,'eqflip':ef,'gate_swap':swap,'flags':flags}
    if score<best:best=score;print('BEST',score,meta,'count',count,'sec',time.time()-start,flush=True)
    if score<=70:
        found.append({'cost':score,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':meta,'word':word})
        (OUT/'candidates.json').write_text(json.dumps(found))
  if count%3200==0:print('PROGRESS',count,'best',best,'found',len(found),'seconds',time.time()-start,flush=True)
(OUT/'receipt.json').write_text(json.dumps({'count':count,'histogram':hist,'best':best,'found':len(found),'seconds':time.time()-start}))
