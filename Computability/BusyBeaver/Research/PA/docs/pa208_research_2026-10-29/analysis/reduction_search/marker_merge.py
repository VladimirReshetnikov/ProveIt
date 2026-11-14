import sys,json,random,time
from pathlib import Path
from discover_folds import read_table,history_contexts

def pi(s,q,r):return r if s==q else s

def row(t,s,b,q,r):
    w,d,z=t[s,b]
    return (1-w,d,r) if z==q else (w,d,z)

def screen(t,q,r,k,c,b,rng,limit):
    if 0 in c and c[0]!=b:return True
    orig={p:rng.randrange(2) for p in range(-limit-3,limit+4)};orig.update(c);orig[0]=b
    w,d,z=t[q,b];expected=dict(orig);expected[0]=w
    if z==q:expected[d+k]=1-expected[d+k]
    tape=dict(orig);tape[k]=1-tape[k]
    s,h=r,0
    for _ in range(limit):
        if s==254:return False
        v,e,s=row(t,s,tape[h],q,r);tape[h]=v;h+=e
        if (s,h)==(pi(z,q,r),d) and tape==expected:return True
    return False

def exact(t,q,r,k,c,b,limit):
    if 0 in c and c[0]!=b:return []
    w,d,z=t[q,b];target=pi(z,q,r)
    c=dict(c);c[0]=b
    stack=[]
    if k not in c:
        for v in(0,1):
            cs=dict(c);cs[k]=v;stack.append((r,0,{k:1-v},cs,[]))
    else:stack=[(r,0,{k:1-c[k]},c,[])]
    cert=[]
    while stack:
        s,h,writes,vals,trace=stack.pop()
        if trace and (s,h)==(target,d):
            positions=set(writes)|{0}
            if z==q:positions.add(d+k)
            def expect(p):
                v=w if p==0 else vals.get(p,('v',p))
                if z==q and p==d+k:v=1-v if isinstance(v,int) else ('not',v)
                return v
            if all(writes.get(p,vals.get(p,('v',p)))==expect(p) for p in positions):
                cert.append({'input':vals,'trace':trace});continue
        if s==254 or len(trace)>=limit:return None
        bit=writes.get(h,vals.get(h))
        if bit is None:
            for v in(0,1):
                vs=dict(vals);vs[h]=v;stack.append((s,h,dict(writes),vs,list(trace)))
            continue
        v,e,z2=row(t,s,bit,q,r);ws=dict(writes);ws[h]=v
        stack.append((z2,h+e,ws,vals,trace+[[s,h,bit,v,e,z2]]))
        if len(stack)+len(cert)>4096:return None
    return cert

def main():
    t=read_table(Path(sys.argv[1]));out=Path(sys.argv[2]);ctx=Path(sys.argv[3]);limit=int(sys.argv[4]) if len(sys.argv)>4 else 31
    cs={int(q):[dict(c)for c in val] for q,val in json.loads(ctx.read_text()).items()}
    states=sorted({s for s,b in t});rng=random.Random(201);results=[];count=0;start=time.monotonic()
    for q in states:
        if q==0:continue
        ds={d for (s,b),(w,d,z) in t.items() if z==q and s!=q}
        if len(ds)!=1:continue
        k=-next(iter(ds))
        for r in states:
            if r==q:continue
            count+=1;inputs=[(c,b)for c in cs[q] for b in(0,1)]
            if not all(screen(t,q,r,k,c,b,rng,limit)for c,b in inputs for _ in range(2)):continue
            cases=[]
            for c,b in inputs:
                cert=exact(t,q,r,k,c,b,limit)
                if cert is None:break
                cases.append({'context':c,'read':b,'branches':cert})
            else:
                print('FOUND',q,r,k,flush=True);results.append({'drop':q,'keep':r,'flipped_cell':k,'cases':cases})
    out.write_text(json.dumps({'count':count,'seconds':time.monotonic()-start,'results':results},indent=2)+'\n');print('DONE',len(results),count,time.monotonic()-start)
if __name__=='__main__':main()
