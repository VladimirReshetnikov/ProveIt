#!/usr/bin/env python3
"""Safe rho8 H/A parameter swap, combined with head order/orientation variants."""
import sys,json,time,collections
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/logic'))
sys.path.insert(0,str(BASE/'work/optimize196'))
import logical_variant_search as v
from layout import *
tree,word,prefix,suffix=v.read_source(ROOT)
prefix=prefix[:6]+[({'node58':'node70','node70':'node58'}.get(x,x)) for x in prefix[6:]]
assert len(prefix)==18
alphabet={t:i for i,t in enumerate(dict.fromkeys(word))}
post=[];cursor=0
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
OUT=Path(__file__).resolve().parent/'rho8_swap';OUT.mkdir(exist_ok=True)
best=999;best_eff=999;start=time.time();hist=collections.Counter();selected=[]
score=v.fixed_association_scorer(tree,alphabet,len(word))
for i,(meta,w) in enumerate(v.word_variants(prefix,suffix)):
    c=score(w);hist[c]+=1
    if c<best:best=c;print('BEST',c,meta,'secs',time.time()-start,flush=True)
    if c<=71:selected.append((c,meta,w))
for j,(c,meta,w) in enumerate(sorted(selected,key=lambda x:x[0])):
    cc,t=instantiate(w);assert cc==c
    rows,index,shape=build(t);ops=opportunities_fast(rows,shape);matching=max_matching(ops);eff=c-len(matching)
    if eff<best_eff:
        best_eff=eff;print('BEST EFFECTIVE',eff,'raw',c,'folds',len(matching),'meta',meta,'secs',time.time()-start,flush=True)
        (OUT/'best.json').write_text(json.dumps(encode(t)))
        (OUT/'best_meta.json').write_text(json.dumps(meta))
        if eff<62:break
(OUT/'receipt.json').write_text(json.dumps({'searched':sum(hist.values()),'best_raw':best,'best_effective':best_eff,'histogram':hist}))
