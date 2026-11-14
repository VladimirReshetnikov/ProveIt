#!/usr/bin/env python3
"""Rebracket the exact PA196 AX macro word with straight-line binary grammars."""
from pathlib import Path
import re, random, collections, json, sys, time

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'sources/BusyBeaver/PA196/Program.lean'
TOKENS = {'node49':'P','node58':'H','node55':'A','node70':'D',
          'node65':'C','node72':'R','node75':'S','node142':'G','node150':'K'}
# These are opaque compression alphabet symbols, not register names:
# token A is node55 (push-and-copy the D register), while token D is node70
# (push-and-copy the A register). The emitted `tokens` map is authoritative.

def parse_defs():
    defs = {}
    for name, expr in re.findall(r'def (\w+) : Tree := (.+)', SRC.read_text()):
        ts = re.findall(r'\.node|\.leaf|\.\w+|[A-Za-z][A-Za-z0-9]*|[0-9]+|\(|\)',expr)
        def term(i):
            if ts[i] == '(':
                t, i = term(i+1)
                assert ts[i] == ')'
                return t,i+1
            if ts[i] == '.node':
                l,i = term(i+1); r,i = term(i)
                return (l,r),i
            if ts[i] == '.leaf':
                assert ts[i+1] == '('
                op = ts[i+2]
                if ts[i+3] == ')': return (op,None),i+4
                assert ts[i+4] == ')'
                return (op,int(ts[i+3])),i+5
            return ts[i],i+1
        defs[name],end = term(0)
        assert end == len(ts),(name,end,ts)
    return defs

DEFS = parse_defs()
def word(t):
    if isinstance(t,str):
        if t in TOKENS:return [TOKENS[t]]
        return word(DEFS[t])
    a,b=t
    if a == '.inc' and b == 1:return ['i']
    if a == '.breakTo' and b == 1:return ['B']
    assert not (isinstance(a,str) and a.startswith('.')),t
    return word(a)+word(b)

WORD=word('x67')

def repaire(seed=0,temperature=0):
    rng=random.Random(seed); seq=list(WORD); rules={}; sig={}; counter=0
    while len(seq)>1:
        counts=collections.Counter(zip(seq,seq[1:]))
        # Pair replacing counts, not overlapping counts.
        for x,y in list(counts):
            if x==y:
                counts[x,y]=sum(len(list(g))//2 for v,g in __import__('itertools').groupby(seq) if v==x)
        best=max(counts.values())
        weights={pair:(freq-1)/(1+0.001*rng.random()) for pair,freq in counts.items()}
        if temperature:
            for p in weights:weights[p]+=rng.random()*temperature
        target=max(weights,key=weights.get)
        if best < 2: break
        # Often choose among ties, occasionally a near-tie.
        if target not in sig:
            name=f'r{counter}';counter+=1
            rules[name]=target;sig[target]=name
        else:name=sig[target]
        out=[];i=0
        while i<len(seq):
            if i+1<len(seq) and (seq[i],seq[i+1])==target:
                out.append(name);i+=2
            else:out.append(seq[i]);i+=1
        seq=out
    # DP optimal concatenation of remaining word, taking existing pairs free.
    # Width small (<70), but active trial cost matters, so greedy shared pairs
    # followed by a balanced tree is acceptable as a first stage.
    def finish(xs):
        nonlocal counter
        if len(xs)==1:return xs[0]
        m=len(xs)//2;l=finish(xs[:m]);r=finish(xs[m:]);p=(l,r)
        if p not in sig:
            name=f'r{counter}';counter+=1;rules[name]=p;sig[p]=name
        return sig[p]
    root=finish(seq)
    return rules,root

def expand(rules,root):
    if root not in rules:return [root]
    a,b=rules[root]
    return expand(rules,a)+expand(rules,b)

def height(rules,root):
    if root not in rules:return 0
    return 1+max(height(rules,q) for q in rules[root])

if __name__=='__main__':
    trials=int(sys.argv[1]) if len(sys.argv)>1 else 5000
    best=1000;t0=time.time()
    print('Word length',len(WORD),'word',''.join(WORD),flush=True)
    for seed in range(trials):
        rules,root=repaire(seed,0.0 if seed%2 else 1.5)
        assert expand(rules,root)==WORD
        if len(rules)<best:
            best=len(rules)
            data={'nodes':best,'seed':seed,'height':height(rules,root),'root':root,
                  'rules':rules,'tokens':TOKENS,'word':WORD}
            Path(__file__).with_name('best.json').write_text(json.dumps(data,indent=2))
            print('best',best,'seed',seed,'height',data['height'],'elapsed',round(time.time()-t0,3),flush=True)
    print('done',round(time.time()-t0,3),flush=True)
