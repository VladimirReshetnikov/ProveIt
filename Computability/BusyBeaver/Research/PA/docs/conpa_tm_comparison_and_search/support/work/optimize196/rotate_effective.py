from layout import *
import random,math,time

ns=raw_nodes()
def tree(s):
    if isinstance(s,str) and s.startswith('x'):
        a,b=ns[s];return (tree(a),tree(b))
    return s
initial=tree('x67')
macroattrs={}
def attrs(t):
    if isinstance(t,str):
        if t in macroattrs:return macroattrs[t]
        ans=attrs(ns[t]);macroattrs[t]=ans;return ans
    if not isnode(t):return (0,0,0)
    h1,l1,m1=attrs(t[0]);h2,l2,m2=attrs(t[1])
    return (1+max(h1,h2),l1+1,max(1+l1,m1,m2))
for m in MACROS:attrs(m)

def stats(t):
    intern={}
    def rec(t):
        if not isnode(t):return attrs(t)
        if t in intern:return intern[t]
        h1,l1,m1=rec(t[0]);h2,l2,m2=rec(t[1]);a=(1+max(h1,h2),l1+1,max(1+l1,m1,m2));intern[t]=a;return a
    a=rec(t)
    return len(intern),a,list(intern)
def replace(t,x,y):
    if t==x:return y
    if isnode(t):return (replace(t[0],x,y),replace(t[1],x,y))
    return t
def rotate_occurrence(t):
    paths=[]
    def collect(s,p):
        if isnode(s):
            if isnode(s[0]) or isnode(s[1]):paths.append(p)
            collect(s[0],p+(0,));collect(s[1],p+(1,))
    collect(t,())
    p=random.choice(paths)
    def rec(s,p):
        if not p:return random.choice(list(rotations(s)))
        if p[0]:return (s[0],rec(s[1],p[1:]))
        return (rec(s[0],p[1:]),s[1])
    return rec(t,p)
def rotations(t):
    if isnode(t[0]):
        a,b=t[0];yield (a,(b,t[1]))
    if isnode(t[1]):
        b,c=t[1];yield ((t[0],b),c)
def encode(t):
    rs={};idx={}
    def rec(t):
        if not isnode(t):return t
        if t in idx:return idx[t]
        l,r=map(rec,t);n=f'g{len(rs)}';rs[n]=[l,r];idx[t]=n;return n
    rt=rec(t);return {'root':rt,'rules':rs}
def cost(t):
    n,(h,l,m),choices=stats(t)
    if m>6 or h>38:return (n+max(0,m-6)*2+max(0,h-38),n,0,choices)
    r,idx,sh=build(t);ops=opportunities_fast(r,sh);folds=len(max_matching(ops))
    return (n-folds,n,folds,choices)

best=cost(initial)[0];best_tree=initial;start=time.time()
print('initial',cost(initial)[:3],flush=True)
for cycle in range(1000):
    t=best_tree;c,n,f,choices=cost(t)
    for j in range(3000):
        node=random.choice(choices);rs=list(rotations(node))
        if not rs:continue
        nt=replace(t,node,random.choice(rs)) if random.random()<0.6 else rotate_occurrence(t)
        nc,nn,nf,nchoices=cost(nt)
        temp=0.1+0.7*(1-j/3000)
        diff=nc-c
        if diff<=0 or random.random()<math.exp(-diff/temp):
            t,c,n,f,choices=nt,nc,nn,nf,nchoices
            if c<best:
                best=c;best_tree=t
                print('BEST',best,'nodes',n,'folds',f,'cycle',cycle,'iteration',j,'secs',time.time()-start,flush=True)
                Path(f'effective_{best}.json').write_text(json.dumps(encode(t),indent=2))
                if best<62:raise SystemExit()
    print('cycle',cycle,'best',best,'secs',time.time()-start,flush=True)
