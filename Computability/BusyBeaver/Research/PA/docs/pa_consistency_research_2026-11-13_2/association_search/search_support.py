"""Portable subset of the original reader-layout search dependencies.

Search scoring only; no consistency or implementation certificate follows.
Derived from the supplied PA research tools. See included licences.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import ast,re,json
ROOT=Path(__file__).resolve().parent/'reference'
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61,'node60':99,'node61':190}
BREAK=('leaf','breakTo',1)
ENTRY_CONTEXT={'node72':0,'node142':1}
def machine():
    labels = ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])', (ROOT/'PA196/Conjugacy.lean').read_text())[1])
    rows={}
    for ln in (ROOT/'data/pa196.tm').read_text().splitlines():
        q,b,w,d,n=ln.split()
        rows[labels[int(q)],int(b)] = (int(w),d=='R',labels[int(n)])
    return rows, labels

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

def read_grammar(path):
    d=json.loads(Path(path).read_text());rs=d['rules']
    def rec(x):
        if isinstance(x,list):return tuple(x)
        if x in rs:return tuple(rec(y) for y in rs[x])
        return x
    return rec(d['root'])

def isnode(t):return isinstance(t,tuple) and len(t)==2

def build(t):
    old,labels=machine()
    rows={(q,b):a for (q,b),a in old.items() if q<1300}
    index={};shape={}
    def state(t):
        if t in MACROS:return MACROS[t]
        if t in index:return index[t]
        assert isnode(t),t
        q=2000+len(index);index[t]=q;shape[q]=t
        for b,c in enumerate(t):
            rows[q,b]=(0,False,302) if c==BREAK else (b,True,state(c))
        return q
    root=state(t);rows[101,1]=(1,True,root)
    return rows,index,shape

def opportunities_fast(rows,shape,ignore_incoming=frozenset()):
    incoming=defaultdict(set)
    for (q,b),tr in rows.items():
        if q not in ignore_incoming and tr[1] and tr[0]==b and tr[2] in shape:incoming[tr[2]].add(b)
    providers=[defaultdict(list),defaultdict(list)]
    for h in {q for q,_ in rows}:
        w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
        if w0 or w1!=1 or not d0 or not d1:continue
        for bit in (0,1):
            if (u0,bit) in rows and (u1,bit) in rows:
                providers[bit][(rows[u0,bit],rows[u1,bit])].append((h,u0,u1))
    left=[q for q in shape if incoming[q]=={0}]
    right=[q for q in shape if incoming[q]=={1}]
    candidates=[]
    for a in left:
        for b in right:
            opts=[]
            for bit in (0,1):
                if rows[a,bit]==rows[b,bit]:opts.append([rows[a,bit]])
                else:opts.append([(bit,False,h) for h,u0,u1 in providers[bit].get((rows[a,bit],rows[b,bit]),[]) if not {a,b}&{h,u0,u1}])
            if all(opts):candidates.append((a,b,opts))
    return candidates

def max_matching(ops):
    edges=defaultdict(list)
    for a,b,o in ops:edges[a].append(b)
    match={}
    def augment(a,seen):
        for b in edges[a]:
            if b in seen:continue
            seen.add(b)
            if b not in match or augment(match[b],seen):match[b]=a;return True
        return False
    for a in edges:augment(a,set())
    return [(a,b) for b,a in match.items()]

RAW=raw_nodes()
@lru_cache(None)
def attrs(t):
    if isinstance(t,str):return attrs(RAW[t])
    # Increment1 temporarily adds a zero after its instruction path.
    if not isnode(t):return (0,1,1) if t==('leaf','inc',1) else (0,0,0)
    ha,la,ma=attrs(t[0]);hb,lb,mb=attrs(t[1])
    return 1+max(ha,hb),1+la,max(1+la,ma,mb)

def encode(t):
    rules={};idx={}
    def rec(t):
        if not isnode(t):return t
        if t in idx:return idx[t]
        a,b=map(rec,t);n=f'g{len(rules)}';rules[n]=[a,b];idx[t]=n;return n
    root=rec(t);return {'root':root,'rules':rules}
