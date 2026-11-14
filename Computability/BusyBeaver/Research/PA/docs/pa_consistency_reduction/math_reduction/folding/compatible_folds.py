#!/usr/bin/env python3
"""Select simultaneous predecessor-bit folds with exact two-cell validation.

Each folded transition is checked on its known predecessor bit and scanned
bit. Reading a third cell before the original one-step endpoint is rejected.
This catches helper folding conflicts and cyclic virtual expansions directly.
"""
from pathlib import Path
import sys,json,collections,itertools,time
WORK=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(WORK/'verification'))
import symbolic as S
import compile_grammar as C
import optimize_extended as O

def decode_data(data):
    def dec(q):return tuple(map(dec,data['rules'][q])) if q in data['rules'] else q
    return dec(data['root'])

def candidates(m,new,tags_from=None):
    tags=collections.defaultdict(set)
    for (q,b),(w,d,r) in (m if tags_from is None else tags_from).items():tags[r].update([w] if d==1 else [0,1])
    pure={q for q,b in m if m[q,0][:2]==(0,1) and m[q,1][:2]==(1,1)}
    helpers=[collections.defaultdict(list),collections.defaultdict(list)]
    for b in [0,1]:
        for h in sorted(pure):
            a=m[h,0][2];c=m[h,1][2]
            if (a,b) in m and (c,b) in m:
                helpers[b][m[a,b],m[c,b]].append((h,a,c))
    left=[q for q in new if q in pure and tags[q]=={0}]
    right=[q for q in new if q in pure and tags[q]=={1}]
    out=[]
    for q in sorted(left):
        for r in sorted(right):
            opts=[]
            for b in [0,1]:
                if m[q,b]==m[r,b]:opts.append([None]);continue
                hs=[h for h,a,c in helpers[b][m[q,b],m[r,b]] if q not in(h,a,c) and r not in(h,a,c)]
                if not hs:break
                opts.append(hs)
            else:
                for ds in itertools.product(*opts):out.append((q,r,ds))
    return out

def fold(m,selected):
    mapping={r:q for q,r,ds in selected};rows={}
    for q,r,ds in selected:
        for b,h in enumerate(ds):rows[q,b]=m[q,b] if h is None else (b,-1,h)
    raw=m|rows
    return {k:(w,d,mapping.get(z,z)) for k,(w,d,z) in raw.items() if k[0] not in mapping},mapping

def check_local(m,selected,record=False):
    mm,mu=fold(m,selected);alltraces=[]
    for q,r,ds in selected:
        for predecessor,orig in enumerate((q,r)):
            for b in [0,1]:
                target=(mu.get(m[orig,b][2],m[orig,b][2]),1)
                tape={-1:predecessor,0:b};state=mu.get(orig,orig);head=0;seen=set();trace=[]
                for step in range(2000):
                    if step and (state,head)==target and tape=={-1:predecessor,0:b}:break
                    conf=(state,head,tape[-1],tape[0])
                    if conf in seen or head not in tape or (state,tape[head]) not in mm:
                        return False,(orig,predecessor,b,conf,target,trace)
                    seen.add(conf)
                    row=mm[state,tape[head]];trace.append((state,head,tape[head],row))
                    tape[head],direction,state=row;head+=direction
                else:return False,(orig,predecessor,b,'fuel')
                if record:alltraces.append((orig,predecessor,b,trace))
    return True,alltraces

def best_subset(m,options,minimum=0):
    # Group alternate helpers for an endpoint pair.
    pair_options=collections.defaultdict(list)
    for q,r,ds in options:pair_options[q,r].append((q,r,ds))
    pairs=sorted(pair_options)
    best=[];tested=0
    def dfs(i,used,selected):
        nonlocal best,tested
        if len(selected)+len(pairs)-i<=len(best):return
        if i==len(pairs):
            tested+=1
            if len(selected)>len(best) and check_local(m,selected)[0]:best=selected.copy()
            return
        q,r=pairs[i]
        if q not in used and r not in used:
            for item in pair_options[q,r]:dfs(i+1,used|{q,r},selected+[item])
        dfs(i+1,used,selected)
    dfs(0,set(),[])
    return best,tested

def analyze(path):
    data=json.loads(Path(path).read_text());grammar=decode_data(data)
    m,t,new,entry=C.compile_grammar(data)
    opts=candidates(m,new.values());sel,tested=best_subset(m,opts)
    extra=max(0,O.zero_shape(grammar)[1]-6)
    return m,t,sel,dict(file=str(path),new_nodes=len(new),options=len(opts),valid_folds=len(sel),
        states=len(m)//2-len(sel)+extra,extra_scanner=extra,subsets_tested=tested,folds=sel)

if __name__=='__main__':
    for p in sys.argv[1:]:
        m,t,s,result=analyze(p);print(json.dumps(result),flush=True)
