#!/usr/bin/env python3
"""UNPROVED calculus variant: (exists H H) -> H, with binder code H fresh in H."""
from pathlib import Path
exec(Path(__file__).with_name('fuse_h2.py').read_text().split("joint='joint'")[0])
for j in range(12):intern(read_grammar(BASE/'work/optimize196'/f'transport_candidates_local_{j}.json'))
byfirst.clear()
for q,w in enumerate(words):byfirst[w[0]].append(q)
OUT=Path(__file__).resolve().parent/'fresh_h1';OUT.mkdir(exist_ok=True)
orders=list(itertools.permutations(range(6)));random.Random(137).shuffle(orders);orders.remove(tuple(range(6)));orders.insert(0,tuple(range(6)))
best=999;found=[];hist=collections.Counter();count=0;start=time.time()
for order in orders:
  for ef,swap,flags,r in itertools.product([False,True],[False,True],range(8),'HDA'):
    hs=v.heads(flags,ef,False);hs[0]=v.I(v.exists(r,r),r)
    word=prefix+sum((v.emit(hs[j]) for j in order),[])+v.emit(v.gate(swap,ef,False))+suffix
    assert len(word)==197
    score,p=parse(word,8);hist[score]+=1;count+=1
    m={'order':order,'eqflip':ef,'gate_swap':swap,'flags':flags,'h1role':r,'status':'UNPROVED_COMPLETENESS'}
    if score<best:best=score;print('BEST',score,m,'n',count,'sec',time.time()-start,flush=True)
    if score<=68:
        found.append({'cost':score,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':m,'word':word})
  if count%9600==0:print('PROGRESS',count,'best',best,'found',len(found),'sec',time.time()-start,flush=True)
  (OUT/'candidates.json').write_text(json.dumps(found))
(OUT/'receipt.json').write_text(json.dumps({'count':count,'histogram':hist,'best':best,'found':len(found),'seconds':time.time()-start}))
