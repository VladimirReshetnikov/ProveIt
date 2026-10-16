#!/usr/bin/env python3
"""Randomized shared grammars for every closed sequence region of a fixed RM.

This exploratory search preserves the ordered word of closed control routines.
It reports decoder nodes only. No binary-machine count is inferred.
"""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import argparse, importlib.util, json, random, time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('dag_tools', HERE.parent / 'sources/09-decoder-decoder-search-dag_tools.py')
dt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dt)

def read(path):
    obj = json.loads(path.read_text())
    ns = {int(k): tuple(tuple(e) for e in v) for k,v in obj['nodes'].items()}
    return ns, obj['root']

def grammar(seqs, seed, exponent, greedy):
    rng = random.Random(seed)
    words = {i:list(w) for i,w in seqs.items()}
    productions=[]
    while True:
        counts=Counter()
        for w in words.values():
            last={}
            for j,p in enumerate(zip(w,w[1:])):
                if last.get(p,-2) < j-1:
                    counts[p]+=1; last[p]=j
        choices=[p for p,c in counts.items() if c>1]
        if not choices:break
        if greedy:
            mx=max(counts[p] for p in choices)
            choice=rng.choice([p for p in choices if counts[p]==mx])
        else:
            choice=rng.choices(choices,[counts[p]**exponent for p in choices])[0]
        token=('G',len(productions));productions.append(choice)
        for i,w in words.items():
            out=[];j=0
            while j<len(w):
                if tuple(w[j:j+2])==choice:out.append(token);j+=2
                else:out.append(w[j]);j+=1
            words[i]=out
    return words,productions,rng

def build(words, productions, atoms, root, rng, balance):
    ns={};seen={}
    def pair(a,b):
        p=(a,b)
        if p not in seen:seen[p]=len(ns);ns[seen[p]]=p
        return ('N',seen[p])
    @lru_cache(None)
    def stat(e):
        if e[0]!='N':return (0,0,0,1)
        a,b=map(stat,ns[e[1]])
        return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3]
    def bracket(items):
        if len(items)==1:return items[0]
        if balance=='right':return pair(items[0],bracket(items[1:]))
        if balance=='left':return pair(bracket(items[:-1]),items[-1])
        if balance=='random':k=rng.randrange(1,len(items))
        else:
            weights=[stat(e)[3] for e in items]
            total=sum(weights);cum=0;ks=[]
            for k in range(1,len(items)):
                cum+=weights[k-1];ks.append((abs(2*cum-total),k))
            k=min(ks)[1]
        return pair(bracket(items[:k]),bracket(items[k:]))
    @lru_cache(None)
    def edge(e):
        if e[0]=='G':return pair(*map(edge,productions[e[1]]))
        if e[0]=='A':return pair(*map(edge,atoms[e[1]]))
        if e[0]=='S':return bracket(list(map(edge,words[e[1]])))
        return e
    r=edge(root);metric=stat(r)
    return ns,r[1],metric

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=1000)
    ap.add_argument('--start',type=int,default=0);ap.add_argument('--exponent',type=int,default=8)
    ap.add_argument('--balance',default='weighted');ap.add_argument('--greedy',action='store_true')
    ap.add_argument('--output',default='grammar');args=ap.parse_args()
    ns,r=read(HERE/'input/candidate_dag.json');seqs,atoms,root=dt.seq_regions(dt.unfold(ns,r))
    best=(999,999,999);hist=Counter();t0=time.time();wins=[]
    out=HERE/args.output;out.mkdir(exist_ok=True)
    for seed in range(args.start,args.start+args.seeds):
        words,ps,rng=grammar(seqs,seed,args.exponent,args.greedy)
        nn,nr,mt=build(words,ps,atoms,root,rng,args.balance)
        key=(len(nn),mt[1],mt[2]);hist[str(key)]+=1
        # Keep unconstrained and mechanically admissible records distinct.
        if key<best:
            best=key;wins.append([seed,*key]);print('best',wins[-1],flush=True)
            (out/'best_dag.json').write_text(json.dumps({'root':nr,'nodes':nn},indent=2)+'\n')
            (out/'best_recipe.json').write_text(json.dumps({'seed':seed,'args':vars(args),'regions':len(seqs),'productions':ps,'words':words},indent=2)+'\n')
        if len(nn)<203 and mt[1]<=7 and mt[2]<=35:
            (out/f'admissible_{seed}_{len(nn)}.json').write_text(json.dumps({'root':nr,'nodes':nn},indent=2)+'\n')
    result={'source_decoder_nodes':len(ns),'seed_start':args.start,'trials':args.seeds,
            'exponent':args.exponent,'balance':args.balance,'greedy':args.greedy,
            'best':best,'improvements':wins,'histogram':hist,'seconds':time.time()-t0,
            'scope':'register decoder only; no TM state-count inference'}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='histogram'},indent=2))

if __name__=='__main__':main()
