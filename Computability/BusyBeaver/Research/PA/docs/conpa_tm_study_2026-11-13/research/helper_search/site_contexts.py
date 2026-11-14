import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic

def words(xs,k,blank=False):
    if k<=0:return {()}
    if not xs:return {(0,)*k} if blank else {tuple((n>>i)&1 for i in range(k)) for n in range(1<<k)}
    t,*tail=xs
    if t[0]=='bit':return {(t[1],)+w for w in words(tail,k-1,blank)}
    if t[0]=='box':return {tuple((n>>i)&1 for i in range(k)) for n in range(1<<k)}
    _,b,a,c=t
    if c>=k:return {(b,)*k}
    if not a:return {(b,)*c+w for w in words(tail,k-c,blank)}
    return {(b,)*k}|{(b,)*j+w for j in range(c,k) for w in words(tail,k-j,blank)}

def contexts(r=4,all_states=False,machine=None):
    m=symbolic.load_machine()if machine is None else machine
    ctx={q:set() for q,b in m if all_states or all(m[q,b][:2]==(b,1) for b in (0,1))}
    totals,obs=symbolic.verify(m,collect=True)
    for i,branch,trace in obs:
        for kind,s,row in trace:
            if kind!='step' or s[0] not in ctx:continue
            q,onl,l,rs=s
            assert not onl
            for left in words(l,r,True):
                for right in words(rs,r+1):
                    w=left[::-1]+right
                    ctx[q].add(sum(v<<i for i,v in enumerate(w)))
    return ctx

if __name__=='__main__':
    import json,time
    t=time.time();r=int(sys.argv[1]) if len(sys.argv)>1 else 4
    c=contexts(r,len(sys.argv)>2)
    Path(__file__).with_name('site_contexts.json').write_text(json.dumps({q:sorted(v) for q,v in c.items()}))
    print(sum(map(len,c.values())),time.time()-t)
