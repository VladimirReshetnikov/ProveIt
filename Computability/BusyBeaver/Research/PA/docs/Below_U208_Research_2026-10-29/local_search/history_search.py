#!/usr/bin/env python3
"""Sound finite-history invariants and exhaustive symbolic macro alias search."""
from pathlib import Path
import argparse,json,random,time,hashlib

def read(path):
    t={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    return t

def histories(t,depth=4):
    states=sorted({q for q,b in t});inc={q:[] for q in states}
    for (q,b),(w,d,z) in t.items():
        if z in inc:inc[z].append((q,b,w,d))
    outputs={};counts={}
    for target in states:
        results=set();stack=[(target,0,{}, {},0)];n=0
        while stack:
            q,h,c,f,k=stack.pop();n+=1
            if q==0 or k==depth:
                results.add(tuple(sorted(f.items())))
                if k==depth:continue
            for p,b,w,d in inc[q]:
                x=h-d
                if x in c and c[x]!=w:continue
                nc=dict(c);nc[x]=b
                nf=dict(f)
                if x not in nf:nf[x]=w
                stack.append((p,x,nc,nf,k+1))
        rs=[dict(v) for v in sorted(results,key=len)]
        small=[]
        for f in rs:
            if not any(all(f.get(x)==v for x,v in g.items()) for g in small):small.append(f)
        outputs[target]=small;counts[target]=n
    return outputs,counts

def finite(old,new,q,r,ctx,b,rng,limit):
    if 0 in ctx and ctx[0]!=b:return True
    cs={i:rng.randrange(2) for i in range(-limit-8,limit+9)};cs.update(ctx);cs[0]=b
    ow,od,oz=old[q,b];oz=r if oz==q else oz
    exp=dict(cs);exp[0]=ow
    act=dict(cs);h=0;s=r
    for k in range(limit):
        if s==254:return False
        w,d,z=new[s,act[h]];act[h]=w;h+=d;s=z
        if (s,h)==(oz,od) and act==exp:return True
    return False

def exact(old,new,q,r,ctx,b,limit):
    if 0 in ctx and ctx[0]!=b:return []
    ow,od,oz=old[q,b];oz=r if oz==q else oz
    ctx=dict(ctx);ctx[0]=b
    stack=[(r,0,{},ctx,[])];cert=[]
    while stack:
        s,h,writes,vals,trace=stack.pop()
        if trace and (s,h)==(oz,od):
            positions=set(writes)|{0}
            if all(writes.get(x,vals.get(x,('v',x)))==(ow if x==0 else vals.get(x,('v',x))) for x in positions):
                cert.append({'input':vals,'trace':trace});continue
        if s==254 or len(trace)>=limit:return None
        b1=writes.get(h,vals.get(h))
        if b1 is None:
            for value in (0,1):
                nv=dict(vals);nv[h]=value
                stack.append((s,h,dict(writes),nv,trace))
            continue
        w,d,z=new[s,b1];nw=dict(writes);nw[h]=w
        stack.append((z,h+d,nw,vals,trace+[[s,h,b1,w,d,z]]))
        if len(stack)+len(cert)>4096:return None
    return cert

def aliases(t,ctxs,limit):
    states=sorted({q for q,b in t});rng=random.Random(20261029);results=[]
    for q in states:
        if q==0:continue
        for r in states:
            if r==q:continue
            nt={(s,b):(w,d,r if z==q else z) for (s,b),(w,d,z) in t.items() if s!=q}
            if not all(finite(t,nt,q,r,c,b,rng,limit) for c in ctxs[q] for b in (0,1) for _ in range(2)):continue
            cert=[]
            for c in ctxs[q]:
                for b in (0,1):
                    ex=exact(t,nt,q,r,c,b,limit)
                    if ex is None:break
                    cert.append({'context':c,'read':b,'branches':ex})
                else:continue
                break
            else:
                results.append({'remove':q,'representative':r,'cases':cert});print('ALIAS',q,r,flush=True)
    return results

def main():
    a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--depth',type=int,default=4);a.add_argument('--limit',type=int,default=25);a.add_argument('--output',required=True);a=a.parse_args()
    start=time.monotonic();t=read(a.table);ctxs,counts=histories(t,a.depth)
    result={'input':a.table,'sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'depth':a.depth,'limit':a.limit,'contexts':ctxs,'history_counts':counts}
    print('CONTEXTS',sum(map(len,ctxs.values())),max(map(len,ctxs.values())),flush=True)
    result['aliases']=aliases(t,ctxs,a.limit);result['seconds']=time.monotonic()-start
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print('DONE',len(result['aliases']),result['seconds'])

if __name__=='__main__':main()
