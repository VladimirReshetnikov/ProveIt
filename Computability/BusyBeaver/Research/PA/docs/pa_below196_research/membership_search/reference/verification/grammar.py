from core import *
from collections import Counter
import random

def raw_nodes():
    nodes={}
    for line in (ROOT/'PA196/Program.lean').read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        children=[]
        for op,arg,name in tokens:
            children.append(name if name else ('leaf',op,int(arg) if arg else None))
        assert len(children)==2
        nodes[m[1]]=tuple(children)
    return nodes

def axword():
    nodes=raw_nodes()
    def flat(s):
        if isinstance(s,str) and s.startswith('x'):
            a,b=nodes[s];return flat(a)+flat(b)
        return [s]
    return flat('x67')

def repair(word,seed=0,noise=0):
    random.seed(seed)
    rules={};seq=list(word)
    while len(seq)>1:
        counts=Counter(zip(seq,seq[1:]))
        # net frequency, with randomized tie breaking and occasional noise
        pair=max(counts,key=lambda p:counts[p]+random.random()*noise)
        new=f'g{len(rules)}';rules[new]=pair
        out=[];i=0
        while i<len(seq):
            if i+1<len(seq) and (seq[i],seq[i+1])==pair:out.append(new);i+=2
            else:out.append(seq[i]);i+=1
        seq=out
    return seq[0],rules

if __name__=='__main__':
    w=axword();print('tokens',len(w),Counter(w));print(w)
    best=1000
    for seed in range(10000):
        root,rules=repair(w,seed,noise=1 if seed<5000 else 3)
        if len(rules)<best:
            best=len(rules)
            print('BEST',best,seed,flush=True)
            Path('best_grammar.json').write_text(json.dumps({'root':root,'rules':rules,'seed':seed},indent=2))
