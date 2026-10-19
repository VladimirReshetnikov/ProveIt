#!/usr/bin/env python3
"""Explore permutations of all eight original logical AX rows.

Research code: state costs are measured source DAG costs, not TM bounds.
GEN and its cache read stay first. The C/G/vacuity bundle and gate stay last.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, json, random, sys, time, itertools

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'vendor'))
import theory_backend_experiment as theory

DATA=json.loads((ROOT/'fixtures/original203.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in DATA['nodes'].items()}

@lru_cache(None)
def bounds(e):
    if e[0]!='N': return (e[1] if e[0]=='B' else int(e[0]=='D'),e[1] if e[0]=='C' else 0)
    a,b=NODES[e[1]]; ba,ca=bounds(a);bb,cb=bounds(b)
    return max(ba-1,bb),max(ca,cb-1)

@lru_cache(None)
def normal(e):
    if e[0]!='N':return e
    a,b=NODES[e[1]];aa,bb=normal(a),normal(b)
    if bounds(a)==bounds(b)==(0,0):
        return ('S',*(aa[1:] if aa[0]=='S' else (aa,)),*(bb[1:] if bb[0]=='S' else (bb,)))
    return ('A',aa,bb)

def word(node):
    n=normal(('N',node))
    assert bounds(('N',node))==(0,0)
    return n[1:] if n[0]=='S' else (n,)

MACROS={166:word(43),121:word(48),168:word(63),171:word(39),177:word(91),
        119:word(57),181:word(79),180:word(58),182:word(57)+(('I',1),)*3,
        218:word(91)+word(57),176:word(60),158:word(18),208:word(30)}
MACROS[178]=MACROS[218]+MACROS[119]+MACROS[218]
MACROS[183]=MACROS[218]+MACROS[180]+MACROS[218]

SPEC,_=theory.published_spec()
ROWS=SPEC['ax_rows']('a','h','b','c','u')
ROW_WORDS=[tuple(t for m in theory.emit(row) for t in MACROS[m]) for row in ROWS[1:]]
PREFIX=tuple(t for m in [166,121,180,176] for t in MACROS[m])

def regions():
    seqs={};atoms={}
    def go(t):
        if t[0]=='S':
            w=tuple(go(e) for e in t[1:])
            if w not in seqs:seqs[w]=len(seqs)
            return ('S',seqs[w])
        if t[0]=='A':
            p=go(t[1]),go(t[2])
            if p not in atoms:atoms[p]=len(atoms)
            return ('A',atoms[p])
        return t
    root=go(normal(('N',DATA['root'])))
    return {i:w for w,i in seqs.items()},{i:p for p,i in atoms.items()},root

SEQS,ATOMS,REGIONROOT=regions()
LONG=max(SEQS,key=lambda i:len(SEQS[i]))
# Map actual normal-form atoms onto the same sequence/control dictionary.
def map_normal(t):
    if t[0]=='S':
        v=tuple(map_normal(e) for e in t[1:])
        return ('S',next(i for i,w in SEQS.items() if w==v))
    if t[0]=='A':
        v=map_normal(t[1]),map_normal(t[2])
        return ('A',next(i for i,p in ATOMS.items() if p==v))
    return t
PREFIX=tuple(map_normal(t) for t in PREFIX)
ROW_WORDS=[tuple(map_normal(t) for t in row) for row in ROW_WORDS]
BEFORE=PREFIX+sum(ROW_WORDS,())
assert SEQS[LONG][:len(BEFORE)]==BEFORE, 'AX logical prefix does not equal original203'
SUFFIX=SEQS[LONG][len(BEFORE):]
ALPHABET=sorted(set(e for w in SEQS.values() for e in w))
ENCODE={e:i for i,e in enumerate(ALPHABET)}
BASEWORDS=[tuple(ENCODE[e] for e in SEQS[i]) for i in range(len(SEQS))]
PREFIX=tuple(ENCODE[e] for e in PREFIX)
ROW_WORDS=[tuple(ENCODE[e] for e in w) for w in ROW_WORDS]
SUFFIX=tuple(ENCODE[e] for e in SUFFIX)

def compress(words,rng,noise=0.0):
    ws=[list(w) for w in words];rules={}
    while any(len(w)>1 for w in ws):
        counts=Counter()
        for w in ws:
            last={}
            for i,p in enumerate(zip(w,w[1:])):
                if last.get(p,-2)+1<i:
                    counts[p]+=1;last[p]=i
        best=max(counts.values())
        candidates=[p for p,c in counts.items() if c>=best-noise]
        pair=rng.choice(candidates)
        n=len(ALPHABET)+len(rules);rules[n]=pair
        nw=[]
        for w in ws:
            out=[];i=0
            while i<len(w):
                if i+1<len(w) and (w[i],w[i+1])==pair:out.append(n);i+=2
                else:out.append(w[i]);i+=1
            nw.append(out)
        ws=nw
    return rules,tuple(w[0] for w in ws)

def emit(rules,roots):
    nodes={};intern={}
    def pair(a,b):
        p=a,b
        if p not in intern:intern[p]=len(nodes);nodes[len(nodes)]=p
        return ('N',intern[p])
    @lru_cache(None)
    def token(t):
        if t<len(ALPHABET):return edge(ALPHABET[t])
        a,b=rules[t];return pair(token(a),token(b))
    @lru_cache(None)
    def edge(e):
        if e[0]=='S':return token(roots[e[1]])
        if e[0]=='A':
            a,b=ATOMS[e[1]];return pair(edge(a),edge(b))
        return e
    root=edge(REGIONROOT)[1]
    @lru_cache(None)
    def measure(e):
        if e[0]!='N':return 0,0,0
        a,b=map(measure,nodes[e[1]])
        p=a[0]+1
        return p,max(p,a[1],b[1]),1+max(a[2],b[2])
    metric=measure(('N',root))
    return nodes,root,(len(nodes),metric[1],metric[2])

def search(runs,seed,out):
    rng=random.Random(seed);best=(999,999,999);history=[];seen=set();beg=time.monotonic()
    out.mkdir(parents=True,exist_ok=True)
    for trial in range(runs):
        if trial==0:order=tuple(range(8))
        elif history and rng.random()<.7:
            order=list(history[-1]['order']);a,b=rng.sample(range(8),2);order[a],order[b]=order[b],order[a];order=tuple(order)
        else:order=tuple(rng.sample(range(8),8))
        seen.add(order)
        words=BASEWORDS.copy();words[LONG]=PREFIX+sum((ROW_WORDS[i] for i in order),())+SUFFIX
        rules,roots=compress(words,rng,trial%5==4)
        nodes,root,metric=emit(rules,roots)
        if metric<best:
            best=metric
            rec=dict(trial=trial,order=order,metrics=metric,seconds=time.monotonic()-beg)
            history.append(rec)
            result=dict(**rec,root=root,nodes=nodes,rules=rules,word_roots=roots)
            (out/'best.json').write_text(json.dumps(result,indent=2)+'\n')
            (out/f'candidate_{trial}_{metric[0]}.json').write_text(json.dumps(result,indent=2)+'\n')
            print('BEST',rec,flush=True)
        if trial%500==0:print('progress',trial,'best',best,'seconds',round(time.monotonic()-beg,1),flush=True)
    result=dict(runs=runs,distinct_orders=len(seen),best=best,seconds=time.monotonic()-beg,history=history)
    (out/'search_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=10000);ap.add_argument('--seed',type=int,default=246018);ap.add_argument('--output',type=Path,default=ROOT/'results/rerun_axiom_order');a=ap.parse_args()
    print('AX row lengths',list(map(len,ROW_WORDS)),'fixed_prefix',len(PREFIX),'suffix',len(SUFFIX),flush=True)
    search(a.runs,a.seed,a.output)
