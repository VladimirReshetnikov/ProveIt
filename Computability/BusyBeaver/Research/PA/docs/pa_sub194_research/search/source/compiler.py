from symbolic_runtime import *

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

from collections import defaultdict

MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61}
MACROS.update({'node60':99,'node61':190})
BREAK=('leaf','breakTo',1)
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

def source(t):
    nodes=raw_nodes();sites=[]
    def walk(t,p):
        if isinstance(t,str):
            if t=='x67':return walk(ax,p)
            return walk(nodes[t],p)
        if t[0]=='leaf':sites.append((p,t[1],t[2]));return
        walk(t[0],p+(0,));walk(t[1],p+(1,))
    ax=t;walk('node172',())
    by_path={p:i for i,(p,op,arg) in enumerate(sites)}
    def locate(p):
        if p in by_path:return by_path[p]
        for i,(q,_,_) in enumerate(sites):
            if q[:len(p)]==p or (p[:len(q)]==q and not any(p[len(q):])):return i
        raise ValueError(p)
    def after(p):
        p=list(p)
        for i in range(len(p)-1,-1,-1):
            if p[i]==0:p[i]=1;return locate(tuple(p[:i+1]))
        raise ValueError(('exit',p))
    def cut(p,b,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==b:
                k-=1
                if not k:return p[:i]
        raise ValueError((p,b,k))
    instructions=[]
    for p,op,arg in sites:
        if op=='inc':ins=('inc',arg,after(p))
        elif op=='dec':ins=('dec',arg,after(cut(p,0,1)),after(p))
        elif op=='breakTo':ins=('jump',after(cut(p,0,arg)))
        elif op=='continueTo':ins=('jump',locate(cut(p,1,arg)))
        elif op=='halt':ins=('halt',)
        else:raise ValueError(op)
        instructions.append(ins)
    cs=[]
    for i,code in enumerate(instructions):
        st=frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;cs.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',PHYSICAL[r])))))
        elif code[0]=='dec':
            _,r,z,p=code
            cs.append((i,(PHYSICAL[r],True),st,canonical(frame(sites[z][0]))))
            cs.append((i,(PHYSICAL[r],False),st,canonical(frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
        elif code[0]=='jump':cs.append((i,None,st,canonical(frame(sites[code[1]][0]))))
        else:cs.append((i,None,st,None))
    return sites,instructions,cs

def opportunities(rows,shape):
    incoming=defaultdict(set)
    for (q,b),tr in rows.items():
        if tr[1] and tr[0]==b and tr[2] in shape:incoming[tr[2]].add(b)
    candidates=[]
    for a,b in itertools.combinations(shape,2):
        opts=[]
        for bit in (0,1):
            if rows[a,bit]==rows[b,bit]:opts.append([rows[a,bit]]);continue
            ac=incoming[a];bc=incoming[b]
            if ac & bc or not ac or not bc:opts.append([]);continue
            optsb=[]
            for h in set(q for q,_ in rows)-{a,b}:
                good=True
                for src,ctx in [(a,ac),(b,bc)]:
                    for p in ctx:
                        w,d,u=rows[h,p]
                        if w!=p or not d or u in (a,b) or rows.get((u,bit))!=rows[src,bit]:
                            good=False;break
                    if not good:break
                if good:optsb.append((bit,False,h))
            opts.append(optsb)
        if all(opts):candidates.append((a,b,opts))
    return candidates

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

def fold(rows,a,b,acts):
    out={}
    for (q,bit),(w,d,n) in rows.items():
        if q==a:continue
        if q==b:w,d,n=acts[bit]
        out[q,bit]=(w,d,b if n==a else n)
    return out



