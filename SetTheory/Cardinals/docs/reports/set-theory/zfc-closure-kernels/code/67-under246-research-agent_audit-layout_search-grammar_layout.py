#!/usr/bin/env python3
"""Global grammar compression of closed sequential decoder regions."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json,sys,random,time,argparse,os

HERE=Path(__file__).resolve().parent
BASE=Path(os.environ.get('BEYOND252_EXPLORATORY',str(HERE.parent.parent/'sources/beyond252/beyond252/exploratory')))
sys.path.insert(0,str(BASE/'vendor'))
import dag_tools as dt
import rotate_search as rot
source=json.loads((BASE/'data/original203.json').read_text())
original={int(i):tuple(map(tuple,p)) for i,p in source['nodes'].items()}
original_root=source['root']
seqs,controls,root=dt.seq_regions(dt.unfold(original,original_root))
alphabet=sorted({e for seq in seqs.values() for e in seq})
encode={e:i for i,e in enumerate(alphabet)}
words=[tuple(encode[e] for e in seqs[i]) for i in range(len(seqs))]

def compress(rng,noise=0.0,top=1):
    ws=[list(w) for w in words];rules={}
    while any(len(w)>1 for w in ws):
        counts=Counter(p for w in ws for p in zip(w,w[1:]))
        if top>1:
            candidates=counts.most_common(top)
            candidates=[(p,c) for p,c in candidates if c>=candidates[0][1]*(1-noise)]
            pair,c=rng.choice(candidates)
        else:
            score=lambda pc:pc[1]+noise*rng.random()
            pair,c=max(counts.items(),key=score)
        n=len(alphabet)+len(rules);rules[n]=pair
        out=[]
        for w in ws:
            new=[];i=0
            while i<len(w):
                if i+1<len(w) and (w[i],w[i+1])==pair:new.append(n);i+=2
                else:new.append(w[i]);i+=1
            out.append(new)
        ws=out
    return rules,[w[0] for w in ws]

def emit(rules,roots):
    nodes={};intern={}
    def pair(a,b):
        p=(a,b)
        if p not in intern:
            intern[p]=len(nodes);nodes[len(nodes)]=p
        return ('N',intern[p])
    @lru_cache(None)
    def token(t):
        if t<len(alphabet):return edge(alphabet[t])
        a,b=rules[t];return pair(token(a),token(b))
    @lru_cache(None)
    def edge(e):
        if e[0]=='S':return token(roots[e[1]])
        if e[0]=='A':
            a,b=controls[e[1]];return pair(edge(a),edge(b))
        return e
    result=edge(root)
    return nodes,result[1]

def verify(rules,roots,nodes,nr):
    @lru_cache(None)
    def expand(t):
        if t<len(alphabet):return (t,)
        a,b=rules[t];return expand(a)+expand(b)
    assert [expand(t) for t in roots]==words
    # Stronger recursive canonicalization: closed association is erased from
    # both complete source expressions, including inside control atoms.
    def canonical(tree):
        if tree[0]!='N':return tree
        a,b=tree[1:]
        if dt.closed(a) and dt.closed(b):
            def flat(e):
                if e[0]=='N' and dt.closed(e[1]) and dt.closed(e[2]):
                    return flat(e[1])+flat(e[2])
                return (canonical(e),)
            return ('S',flat(tree))
        return ('A',canonical(a),canonical(b))
    assert canonical(dt.unfold(nodes,nr))==canonical(dt.unfold(original,original_root))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=1000);ap.add_argument('--seed',type=int,default=203246)
    args=ap.parse_args();rng=random.Random(args.seed);best=(1000,1000,1000);started=time.monotonic();records=[]
    for trial in range(args.runs):
        noise,top=([(0,1),(1,1),(0.05,3),(0.15,4),(0.3,6)][trial%5])
        rules,roots=compress(rng,noise,top);nodes,nr=emit(rules,roots)
        p,z,dep=rot.zero_metrics(nodes,nr);metric=(len(nodes),z,dep)
        if metric<best:
            verify(rules,roots,nodes,nr)
            best=metric;record=dict(trial=trial,metrics=metric,noise=noise,top=top,root=nr,nodes=nodes,rules=rules,word_roots=roots)
            records.append(record);(HERE/'grammar_best.json').write_text(json.dumps(record,indent=2)+'\n')
            print('BEST',trial,metric,'seconds',round(time.monotonic()-started,2),flush=True)
        if len(nodes)<=202 or len(nodes)==203 and z<=6:
            (HERE/f'candidate_{trial}.json').write_text(json.dumps(dict(root=nr,nodes=nodes,metrics=metric,rules=rules,word_roots=roots),indent=2)+'\n')
            print('TARGET',trial,metric,flush=True)
            break
        if trial%100==0:print('progress',trial,'best',best,flush=True)
    (HERE/'grammar_search_result.json').write_text(json.dumps(dict(runs=trial+1,best=best,seconds=time.monotonic()-started,history=records),indent=2)+'\n')

if __name__=='__main__':main()
