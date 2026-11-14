#!/usr/bin/env python3
from grammar_search import *
from collections import Counter

def repair(s,rng,mode=0):
    alphabet=sorted(set(s)); rules={i:c for i,c in enumerate(alphabet)}
    seq=[alphabet.index(c) for c in s]
    while True:
        cnt=Counter(zip(seq,seq[1:]))
        # Actual nonoverlapping count for runs.
        for a,b in list(cnt):
            if a==b:
                n=0; run=0
                for c in seq:
                    if c==a:run+=1
                    else:n+=run//2;run=0
                cnt[a,b]=n+run//2
        can=[(v,k) for k,v in cnt.items() if v>1]
        if not can:break
        if mode==0:
            m=max(v for v,k in can); pair=rng.choice([p for v,p in can if v==m])
        else:
            # Mix greediness with near-greedy choices.
            power=[1,2,4,8,16][mode-1]
            mx=max(v for v,k in can)
            weights=[(v-1)**power for v,k in can]
            pair=rng.choices([k for v,k in can],weights)[0]
        key=len(rules);rules[key]=pair
        out=[];i=0
        while i<len(seq):
            if i+1<len(seq) and (seq[i],seq[i+1])==pair:
                out.append(key);i+=2
            else:out.append(seq[i]);i+=1
        seq=out
    def expand(i):
        q=rules[i]
        return q if isinstance(q,str) else (expand(q[0]),expand(q[1]))
    seq=[expand(i) for i in seq]
    def glue(seq):
        if len(seq)==1:return seq[0]
        k=rng.randrange(1,len(seq))
        return (glue(seq[:k]),glue(seq[k:]))
    return glue(seq)

def context_stats(t):
    ctx={}
    def walk(t,bit=None):
        if isinstance(t,str):return
        ctx.setdefault(t,set()).add(bit)
        walk(t[0],0);walk(t[1],1)
    walk(t)
    return ctx

def overlay_potential(t):
    ctx=context_stats(t)
    left=[n for n,c in ctx.items() if c=={0}]
    right=[n for n,c in ctx.items() if c=={1}]
    graph={a:[b for b in right if a[0]==b[0] or a[1]==b[1]] for a in left}
    # Maximum cardinality matching is upper bound for possible folds.
    mt={}
    def aug(a,seen):
        for b in graph[a]:
            if b in seen:continue
            seen.add(b)
            if b not in mt or aug(mt[b],seen):mt[b]=a;return True
        return False
    for a in left:aug(a,set())
    return len(mt)

def main():
    ns,mac,base=get_macro_tree(); s=word(base)
    best=count(base);bestcost=best-overlay_potential(base)
    print('baseline',best,'potential',overlay_potential(base),flush=True)
    rng=random.Random(98743);start=time.time()
    for i in range(20000):
        mode=0 if i%2 else rng.randrange(1,6)
        t=repair(s,rng,mode);c=count(t)
        if c<best:
            best=c
            print('BEST DAG',c,'potential',overlay_potential(t),'i',i,'sec',time.time()-start,flush=True)
            (OUT/f'repair_best_{c}.json').write_text(json.dumps(t))
        if c<=best+3:
            cost=c-overlay_potential(t)
            if cost<bestcost:
                bestcost=cost
                print('BEST FOLD',c,overlay_potential(t),cost,'i',i,'sec',time.time()-start,flush=True)
                (OUT/f'repair_fold_{cost}.json').write_text(json.dumps(t))
        if time.time()-start>180:break

if __name__=='__main__':main()
