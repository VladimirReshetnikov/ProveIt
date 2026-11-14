#!/usr/bin/env python3
import sys,pathlib,json,random,math,time,itertools,pickle,argparse
P=(pathlib.Path(__file__).resolve().parent / 'reference_pa195')
sys.path.insert(0,str(P));import build_verify as v
c=v.c
OUT=pathlib.Path(__file__).resolve().parent
base=c.read_grammar(P/'grammar.json')
from functools import lru_cache
rawnodes=c.raw_nodes()
@lru_cache(None)
def stats(t):
    if isinstance(t,str):return stats(rawnodes[t])
    if t[0]=='leaf':return 0,0,0
    a,b=stats(t[0]),stats(t[1]);return max(a[0],b[0],1+a[1]),a[1]+1,max(a[2],b[2])+1
raw,_=c.machine();engine={k:a for k,a in raw.items() if k[0]<1300}

def build(t):
    rows=engine.copy();index={};shape={}
    def st(t):
        if t in c.MACROS:return c.MACROS[t]
        if t in index:return index[t]
        q=2000+len(index);index[t]=q;shape[q]=t
        for b,x in enumerate(t):rows[q,b]=(0,False,302) if x==v.BREAK else (b,True,st(x))
        return q
    root=st(t);rows[101,1]=(1,True,root)
    return rows,index,shape

def writegrammar(t,path):
    rules={};memo={}
    def visit(t):
        if not c.isnode(t):return list(t) if isinstance(t,tuple) else t
        if t in memo:return memo[t]
        a,b=visit(t[0]),visit(t[1]);s='g'+str(len(rules));rules[s]=[a,b];memo[t]=s;return s
    root=visit(t);path.write_text(json.dumps({'root':root,'rules':rules},indent=2)+'\n')

def quotient(rows,ops,matching):
    dic={(a,b):o for a,b,o in ops}
    choices=[[(a,b,acts) for acts in itertools.product(*dic[a,b])] for a,b in matching]
    for fs in itertools.islice(itertools.product(*choices),64):
        try:
            folded,aliases=v.quotient(rows,fs);cert=v.quotient_certificate(rows,folded,fs,aliases)
            return folded,fs,cert
        except (ValueError,KeyError):pass
    return None

def evaluates(t,rng):
    rows,index,shape=build(t);ops=c.opportunities_fast(rows,shape);matching=c.max_matching(ops)
    n=len(rows)//2-len(matching)
    return n,len(shape),rows,ops,matching

def nodes(t):
    out=[]
    def walk(t,p):
        if c.isnode(t):
            out.append((t,p));walk(t[0],p+(0,));walk(t[1],p+(1,))
    walk(t,());return out

def repl(t,p,new):
    if not p:return new
    b=p[0];return (repl(t[0],p[1:],new),t[1]) if b==0 else (t[0],repl(t[1],p[1:],new))

def globalrepl(t,old,new):
    if t==old:return new
    if c.isnode(t):return globalrepl(t[0],old,new),globalrepl(t[1],old,new)
    return t

def mutate(t,rng):
    ns=nodes(t)
    for _ in range(10):
        x,p=rng.choice(ns)
        side=rng.randrange(2)
        if not c.isnode(x[side]):continue
        if side==0:
            a,b=x[0];n=(a,(b,x[1]))
        else:
            a,b=x[1];n=((x[0],a),b)
        return globalrepl(t,x,n) if rng.random()<0.6 else repl(t,p,n)
    return t

def signature(t):
    return sum(1 for _ in nodes(t))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed',type=int,default=1);ap.add_argument('--steps',type=int,default=100000);a=ap.parse_args()
    rng=random.Random(a.seed);cur=base;ev=evaluates(cur,rng);best=ev[0];pool=[(base,ev[0])];started=time.time();seen={};accepted=0
    for k in range(a.steps):
        if k%10000==0 and k:
            cur,sc=rng.choice(pool);ev=evaluates(cur,rng)
        cand=mutate(cur,rng)
        if stats(cand)[0]>6 or stats(cand)[2]>39:continue
        if cand in seen:ce=seen[cand]
        else:
            ce=evaluates(cand,rng);seen[cand]=ce[:2]
        n,nodesn=ce[:2];d=n-ev[0];temp=0.03+0.25*(1-(k%10000)/10000)
        if n<=best+3 and (d<0 or rng.random()<math.exp(-d/temp)):
            if len(ce)<3:ce=evaluates(cand,rng)
            cur,ev=cand,ce;accepted+=1
            if n<=best:
                found=quotient(ce[2],ce[3],ce[4])
                if found:
                    if n<best:
                        folded,fs,cert=found;name=f'candidate{n}_s{a.seed}_k{k}';writegrammar(cur,OUT/(name+'.json'));(OUT/(name+'.folds.json')).write_text(json.dumps(fs,indent=2));(OUT/(name+'.native.tm')).write_bytes(v.table_bytes(folded));(OUT/(name+'.certificate.json')).write_text(json.dumps(cert,indent=2))
                        print('NEW',name,'readers',nodesn,'folds',len(fs),'time',round(time.time()-started,2),flush=True)
                    if n<best:
                        best=n;pool=[(cur,n)]
                        if n<195:return
                    elif len(pool)<100:pool.append((cur,n))
        if len(seen)>100000:seen.clear()
        if k%1000==0:print('STATUS',a.seed,k,'current',ev[:2],'best',best,'accepted',accepted,'time',round(time.time()-started,2),flush=True)
    print('DONE',a.seed,best,time.time()-started,flush=True)
if __name__=='__main__':main()
