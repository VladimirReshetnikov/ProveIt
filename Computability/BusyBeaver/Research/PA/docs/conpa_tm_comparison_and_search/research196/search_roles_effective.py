#!/usr/bin/env python3
"""Score state-sharing, rather than raw DAG count, for safe head-role variants."""
import sys,json,time,collections,itertools
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/logic'));sys.path.insert(0,str(BASE/'work/optimize196'))
import logical_variant_search as v
from layout import *
tree,word,prefix,suffix=v.read_source(ROOT)
alphabet={t:i for i,t in enumerate(dict.fromkeys(word))};post=[];cursor=0
def skel(t):
    global cursor
    if not isnode(t):i=cursor;cursor+=1;return i
    a,b=map(skel,t);i=len(word)+len(post);post.append((a,b));return i
rt=skel(tree)
def instantiate(w):
    ids=[alphabet[t] for t in w];rules={};cache=list(alphabet)
    for a,b in post:
        pair=ids[a],ids[b]
        if pair not in rules:rules[pair]=len(cache);cache.append((cache[pair[0]],cache[pair[1]]))
        ids.append(rules[pair])
    return len(rules),cache[ids[rt]]
def encode(t):
    rules={};ids={}
    def rec(t):
        if not isnode(t):return t
        if t in ids:return ids[t]
        a,b=map(rec,t);q='g'+str(len(rules));rules[q]=[a,b];ids[t]=q;return q
    rt=rec(t);return {'root':rt,'rules':rules}
perms=list(itertools.permutations('DHA'));hh=[]
for h in v.heads():
    hw=v.emit(h);hh.append([[{v.VARS[a]:v.VARS[b] for a,b in zip('DHA',p)}.get(t,t) for t in hw] for p in perms])
gg=v.emit(v.gate());score=v.fixed_association_scorer(tree,alphabet,len(word))
best=62;count=0;threshold=int(sys.argv[1]) if len(sys.argv)>1 else 76;start=time.time()
OUT=Path(__file__).resolve().parent/'roles_effective';OUT.mkdir(exist_ok=True)
hist=collections.Counter()
for choices in itertools.product(range(6),repeat=6):
    w=prefix+sum((hh[i][p] for i,p in enumerate(choices)),[])+gg+suffix;c=score(w);hist[c]+=1
    if c>threshold:continue
    count+=1;cc,t=instantiate(w);assert cc==c
    rows,index,shape=build(t);ops=opportunities_fast(rows,shape);matching=max_matching(ops);eff=c-len(matching)
    if eff<best:
        best=eff;print('BEST',best,'raw',c,'folds',len(matching),'choices',choices,'seconds',time.time()-start,flush=True)
        (OUT/f'best_{best}.json').write_text(json.dumps(encode(t)))
        (OUT/f'best_{best}_meta.json').write_text(json.dumps({'choices':choices,'raw':c,'folds':matching}))
        if best<62:break
print('DONE',count,'full scores','best',best,'hist',hist,'seconds',time.time()-start,flush=True)
(OUT/'receipt.json').write_text(json.dumps({'count':count,'all':sum(hist.values()),'threshold':threshold,'best':best,'hist':hist}))
