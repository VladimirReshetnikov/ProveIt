import sys,json,random,time
from pathlib import Path
from discover_folds import read_table,history_contexts

def row(t,s,b,drop,keep,offset):
    w,d,z=t[s,b]
    return (w,d+offset,keep) if z==drop else (w,d,z)

def screen(t,q,r,off,c,b,rng,limit):
    if 0 in c and c[0]!=b:return True
    tape={p:rng.randrange(2) for p in range(-limit-abs(off)-2,limit+abs(off)+3)};tape.update(c);tape[0]=b
    w,d,z=t[q,b];target=r if z==q else z;pos=d+(off if z==q else 0)
    expected=dict(tape);expected[0]=w
    s,h=r,off
    for k in range(limit):
        if s==254:return False
        v,e,s=row(t,s,tape[h],q,r,off);tape[h]=v;h+=e
        if (s,h)==(target,pos) and tape==expected:return True
    return False

def exact(t,q,r,off,c,b,limit):
    if 0 in c and c[0]!=b:return []
    w,d,z=t[q,b];target=r if z==q else z;pos=d+(off if z==q else 0)
    c=dict(c);c[0]=b
    stack=[(r,off,{},c,[])];cert=[]
    while stack:
        s,h,writes,vals,trace=stack.pop()
        if trace and (s,h)==(target,pos):
            if all(writes.get(p,vals.get(p,('v',p)))==(w if p==0 else vals.get(p,('v',p))) for p in set(writes)|{0}):
                cert.append({'input':vals,'trace':trace});continue
        if s==254 or len(trace)>=limit:return None
        bit=writes.get(h,vals.get(h))
        if bit is None:
            for v in(0,1):
                vs=dict(vals);vs[h]=v;stack.append((s,h,dict(writes),vs,list(trace)))
            continue
        v,e,z=row(t,s,bit,q,r,off);ws=dict(writes);ws[h]=v
        stack.append((z,h+e,ws,vals,trace+[[s,h,bit,v,e,z]]))
        if len(stack)+len(cert)>4096:return None
    return cert

def main():
    t=read_table(Path(sys.argv[1]));out=Path(sys.argv[2]);depth=int(sys.argv[3]) if len(sys.argv)>3 else 8
    start=time.monotonic();cs=history_contexts(t,depth);states=sorted({s for s,b in t});rng=random.Random(42);results=[];count=0
    for q in states:
        if q==0:continue
        ds={d for (s,b),(w,d,z)in t.items() if z==q and s!=q}
        if len(ds)!=1:continue
        off=-2*next(iter(ds))
        for r in states:
            if r==q:continue
            count+=1;inputs=[(dict(c),b) for c in cs[q] for b in(0,1)]
            if not all(screen(t,q,r,off,c,b,rng,31) for c,b in inputs for _ in range(2)):continue
            cases=[]
            for c,b in inputs:
                cert=exact(t,q,r,off,c,b,31)
                if cert is None:break
                cases.append({'context':c,'read':b,'branches':cert})
            else:
                print('FOUND',q,r,off,flush=True);results.append({'drop':q,'keep':r,'offset':off,'cases':cases})
    out.write_text(json.dumps({'depth':depth,'count':count,'seconds':time.monotonic()-start,'results':results},indent=2)+'\n')
    print('DONE',len(results),count,time.monotonic()-start)
if __name__=='__main__':main()
