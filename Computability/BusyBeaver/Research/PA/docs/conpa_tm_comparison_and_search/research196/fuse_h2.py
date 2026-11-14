#!/usr/bin/env python3
"""Sound fusion of quantifier commutation into the guarded gate.

If A=D its missing instance is identity. If A=H, replace H by NN(H),
apply the guarded instance, then transport both quantified sides with
the full distribution head and classical H <-> NN(H).
"""
import sys,itertools,json,time,random,collections,heapq
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/logic'));sys.path.insert(0,str(BASE/'work/optimize196'))
import logical_variant_search as v
from layout import *
initial,w,prefix,suffix=v.read_source(ROOT)
trees=[];ids={};words=[];masks=[]
def intern(t):
    if t in ids:return ids[t]
    if isnode(t):
        a,b=map(intern,t);word=words[a]+words[b];mask=masks[a]|masks[b]
    else:word=(t,);mask=0
    q=len(trees);ids[t]=q;trees.append(t);words.append(word);masks.append(mask|(1<<q) if isnode(t) else 0);return q
intern(initial)
byfirst=collections.defaultdict(list)
for q,w in enumerate(words):byfirst[w[0]].append(q)
def parse(word,B=8):
    n=len(word);options=[]
    for i in range(n):options.append([q for q in byfirst[word[i]] if tuple(word[i:i+len(words[q])])==words[q]])
    dp=[{} for _ in range(n+1)];dp[0][0]=()
    for i in range(n):
        beam=heapq.nsmallest(B,dp[i].items(),key=lambda t:t[0].bit_count()+len(t[1]));dp[i]={}
        for mask,parts in beam:
            for q in options[i]:
                j=i+len(words[q]);m=mask|masks[q];p=parts+(q,)
                if m not in dp[j] or len(p)<len(dp[j][m]):dp[j][m]=p
    m,p=min(dp[n].items(),key=lambda t:t[0].bit_count()+len(t[1]))
    return m.bit_count()+len(p)-1,p
def encode(t):
    rs={};index={}
    def rec(t):
        if not isnode(t):return t
        if t in index:return index[t]
        a,b=map(rec,t);q='g'+str(len(rs));rs[q]=[a,b];index[t]=q;return q
    rt=rec(t);return {'root':rt,'rules':rs}
joint='joint' in sys.argv
OUT=Path(__file__).resolve().parent/('fused_h2_h5' if joint else 'fused_h2');OUT.mkdir(exist_ok=True)
best=999;hist=collections.Counter();found=[];start=time.time();count=0
heads_count=4 if joint else 5
orders=list(itertools.permutations(range(heads_count)))
default=tuple(range(heads_count))
random.Random(137).shuffle(orders);orders.remove(default);orders.insert(0,default)
for order in orders:
  for ef,swap,flags in itertools.product([False,True],range(24 if joint else 6),range(8)):
    hs=v.heads(flags,ef,False);fused=[1,4] if joint else [1];moved=[hs[j] for j in fused];kept=[h for i,h in enumerate(hs) if i not in fused]
    delta,vac,q=v.gate_parts(ef,False);parts=list(itertools.permutations(moved+[delta,vac]))[swap]
    word=prefix+sum((v.emit(kept[i]) for i in order),[])+sum(map(v.emit,parts),[])+v.emit(q)+['node65']*len(parts)+['node49',v.INC,'node65']+suffix
    assert len(word)==201+len(fused)
    score,p=parse(word,8);hist[score]+=1;count+=1
    meta={'order':order,'eqflip':ef,'gate_order':swap,'flags':flags}
    if score<best:best=score;print('BEST',score,meta,'count',count,'sec',time.time()-start,flush=True)
    if score<=71:
        found.append({'cost':score,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':meta,'word':word})
        (OUT/'candidates.json').write_text(json.dumps(found))
  if count%960==0:print('PROGRESS',count,'best',best,'found',len(found),'seconds',time.time()-start,flush=True)
(OUT/'receipt.json').write_text(json.dumps({'count':count,'histogram':hist,'best':best,'found':len(found),'seconds':time.time()-start}))
