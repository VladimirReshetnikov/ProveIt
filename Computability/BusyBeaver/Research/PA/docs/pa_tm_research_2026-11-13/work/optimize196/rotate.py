from grammar import *
import math,time

nodes=raw_nodes()
def tree(s):
    if isinstance(s,str) and s.startswith('x'):
        a,b=nodes[s];return (tree(a),tree(b))
    return s
initial=tree('x67')
def isnode(t):return isinstance(t,tuple) and len(t)==2
def stats(t):
    intern={};counts=Counter()
    def rec(t):
        if not isnode(t):return 0
        counts[t]+=1
        if t in intern:return intern[t]
        h=1+max(rec(t[0]),rec(t[1]));intern[t]=h;return h
    h=rec(t)
    return len(intern),h,list(intern)
def replace(t,x,y):
    if t==x:return y
    if isnode(t):return (replace(t[0],x,y),replace(t[1],x,y))
    return t
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
    rt=rec(t)
    return {'root':rt,'rules':rs}

best=stats(initial)[0];start=time.time()
print('initial',stats(initial)[:2],flush=True)
best_tree=initial
for cycle in range(100):
    t=best_tree if cycle%3!=2 else initial;n,h,choices=stats(t)
    for j in range(40000):
        node=random.choice(choices);rots=list(rotations(node))
        if not rots:continue
        nt=replace(t,node,random.choice(rots));nn,nh,nchoices=stats(nt)
        if nh>30:continue
        temp=0.15+0.7*(1-(j%10000)/10000)
        cost=nn-n
        if cost<=0 or random.random()<math.exp(-cost/temp):
            t,n,h,choices=nt,nn,nh,nchoices
            if n<best:
                best=n;best_tree=t
                print('BEST',best,'height',h,'cycle',cycle,'iter',j,'secs',time.time()-start,flush=True)
                Path('best_rotation.json').write_text(json.dumps(encode(t),indent=2))
    print('cycle',cycle,'best',best,'secs',time.time()-start,flush=True)
