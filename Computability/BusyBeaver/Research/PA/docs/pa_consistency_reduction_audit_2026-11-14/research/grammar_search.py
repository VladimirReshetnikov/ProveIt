#!/usr/bin/env python3
"""Explore associative recompression of the pinned PA196 axiom body.

Exploratory only: equality of ordinal source graphs is checked for saved
improvements; binary compilation and PA equivalence remain separate.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import sys, random, json, time, argparse

BASE=Path(__file__).resolve().parents[1]/'ProveIt/Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search'
sys.path.insert(0,str(BASE))
import scan_rotations as s

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=1000);ap.add_argument('--seed',type=int,default=731)
    ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--out',type=Path,default=Path(__file__).with_name('grammar'))
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    names={v:k for k,v in s.env.items()};rng=random.Random(args.seed)
    root=s.root; target=s.env['x64'];oldgraph=s.graph(root)
    @lru_cache(None)
    def flatten(t):
        if names.get(t,'').startswith('x'):
            return flatten(s.store[t][1])+flatten(s.store[t][2])
        return (t,)
    # All closed x nodes that have a reference from outside the axiom body
    # are compressed alongside the main word, retaining potential sharing.
    outside=s.unique(root)-s.unique(target)
    auxiliary=[]
    for t in outside:
        if s.isnode(t):
            for ch in s.store[t][1:]:
                if ch in s.unique(target) and names.get(ch,'').startswith('x'):
                    auxiliary.append(ch)
    roots=[target]+sorted(set(auxiliary));original=[flatten(t) for t in roots]
    best=159; hist=Counter();start=time.monotonic()
    def balanced(xs):
        if len(xs)==1:return xs[0]
        j=len(xs)//2
        return s.node(balanced(xs[:j]),balanced(xs[j:]))
    def encode(t):
        z=s.store[t]
        return [z[0],z[1]] if not s.isnode(t) else [encode(z[1]),encode(z[2])]
    for run in range(args.runs):
        if time.monotonic()-start>args.seconds:break
        words=[list(x) for x in original]
        temp=rng.choice([0,0.03,0.1,0.3,0.6,1.0,1.5])
        while True:
            counts=Counter(pair for w in words for pair in zip(w,w[1:]))
            options=[(p,n) for p,n in counts.items() if n>1]
            if not options:break
            pair,n=max(options,key=lambda x:x[1]+temp*rng.expovariate(1))
            new=s.node(*pair)
            for i,w in enumerate(words):
                j=0;out=[]
                while j<len(w):
                    if j+1<len(w) and (w[j],w[j+1])==pair:out.append(new);j+=2
                    else:out.append(w[j]);j+=1
                words[i]=out
        replacements={t:balanced(w) for t,w in zip(roots,words)}
        @lru_cache(None)
        def rebuild(t):
            if t in replacements:return replacements[t]
            if not s.isnode(t):return t
            return s.node(*(rebuild(ch) for ch in s.store[t][1:]))
        candidate=rebuild(root);cost=s.metric(candidate);hist[cost]+=1
        if cost<best:
            assert s.graph(candidate)==oldgraph
            best=cost
            data=encode(candidate)
            (args.out/f'source{cost}.tree.json').write_text(json.dumps(data)+'\n')
            m={'run':run,'internal_nodes':cost,'source_sites':len(list(s.leaf_occurrences(candidate))),
               'max_zero_run':max(max(map(len,''.join(map(str,p)).split('1'))) for p,t in s.leaf_occurrences(candidate)),
               'max_path':max(len(p) for p,t in s.leaf_occurrences(candidate)),
               'graph_equal':True,'seed':args.seed,'temperature':temp}
            (args.out/f'source{cost}.json').write_text(json.dumps(m,indent=2)+'\n');print(m,flush=True)
        # Interned objects from unsuccessful samples can be reclaimed without
        # changing original ids; successful files retain self-contained trees.
        if len(s.store)>100000:
            s.store[:]=s.store[:len0];s.intern.clear();s.intern.update({t:i for i,t in enumerate(s.store)})
            s.bound.cache_clear()
    receipt={'runs':sum(hist.values()),'seed':args.seed,'best':best,'histogram':dict(sorted(hist.items())),
             'macro_word_lengths':[len(w) for w in original],'elapsed_seconds':time.monotonic()-start}
    (args.out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)

len0=len(s.store)
if __name__=='__main__':main()
