#!/usr/bin/env python3
"""Discover local aliases using exhaustive finite-history tape contexts.

Contexts are generated for all states with arbitrary tape, then tightened by
each transition.  Early configurations from state 0 are included separately.
Every accepted context case is a symbolic identity with unbounded untouched
tape exterior.  Positive macro blocks preserve the input-to-halt relation.
"""
import argparse,json,random,time
from pathlib import Path

def read(p):
    t={}
    for l in Path(p).read_text().splitlines():
        if not l or l.startswith('#'): continue
        q,b,w,d,z=l.split();t[int(q),int(b)]=int(w),1 if d=='R' else -1,int(z)
    return t

def advance(t,ctx):
    out=set()
    for q,c in ctx:
        if q==254: continue
        v=dict(c)
        for b in ([v[0]] if 0 in v else [0,1]):
            w,d,z=t[q,b]
            new={p-d:b0 for p,b0 in v.items()};new[-d]=w
            out.add((z,tuple(sorted(new.items()))))
    return out

def contexts(t,depth):
    states=sorted({q for q,b in t})
    frontier={(q,()) for q in states}
    early={(0,())}; prefix={(0,())}
    for i in range(depth):
        frontier=advance(t,frontier)
        prefix=advance(t,prefix)
        early.update(prefix)
        print('history',i+1,'contexts',len(frontier),'early',len(early),flush=True)
    result={q:set() for q in states}
    for q,c in frontier|early:
        if q in result: result[q].add(c)
    # Remove stronger contexts subsumed by a weaker context for the same state.
    for q,cs in result.items():
        keep=[]
        for c in sorted(cs,key=len):
            f=frozenset(c)
            if not any(x.issubset(f) for x in keep): keep.append(f)
        result[q]=[dict(c) for c in keep]
    return result

def screen(t,q,r,context,rng,limit):
    cells={i:rng.randrange(2) for i in range(-limit-4,limit+5)}
    cells.update(context)
    b=cells[0];ow,od,oz=t[q,b];target=r if oz==q else oz
    expected=dict(cells);expected[0]=ow
    actual=dict(cells);p=0;s=r
    for k in range(1,limit+1):
        if s==254:return False
        w,d,z=t[s,actual[p]]
        actual[p]=w;p+=d;s=r if z==q else z
        if (s,p)==(target,od) and actual==expected:return True
    return False

def exact(t,q,r,context,limit):
    result=[]
    for oldbit in ([context[0]] if 0 in context else [0,1]):
        initial=dict(context);initial[0]=oldbit
        ow,od,oz=t[q,oldbit];target=r if oz==q else oz
        stack=[(r,0,{},initial,[])];cert=[]
        while stack:
            s,p,writes,values,trace=stack.pop()
            if trace and (s,p)==(target,od):
                positions=set(writes)|{0}
                if all(writes.get(x,values.get(x,('v',x)))==(ow if x==0 else values.get(x,('v',x))) for x in positions):
                    cert.append({'initial':values,'trace':trace,'target':[target,od]});continue
            if len(trace)>=limit or s==254:return None
            bit=writes.get(p,values.get(p))
            if bit is None:
                for b in (0,1):
                    v=dict(values);v[p]=b
                    stack.append((s,p,dict(writes),v,list(trace)))
                continue
            w,d,z=t[s,bit];z=r if z==q else z
            wn=dict(writes);wn[p]=w
            stack.append((z,p+d,wn,values,trace+[[s,p,bit,w,d,z]]))
            if len(stack)+len(cert)>16384:return None
        result.append({'oldbit':oldbit,'branches':cert})
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('--depth',type=int,default=5);p.add_argument('--limit',type=int,default=25);p.add_argument('--output',required=True);a=p.parse_args()
    began=time.monotonic();t=read(a.table);cs=contexts(t,a.depth)
    rng=random.Random(2347618);states=sorted(cs);success=[];screened=0
    known0={q:sorted({c.get(0,2) for c in contexts}) for q,contexts in cs.items()}
    print('known scanned', {q:v for q,v in known0.items() if v!=[2] and 2 not in v},flush=True)
    for q in states:
        if q==0:continue
        if not cs[q]:print('UNREACHABLE',q,flush=True);continue
        ordered=sorted(cs[q],key=lambda c:(len(c),str(c)))
        for r in states:
            if r==q:continue
            screened+=1
            if not all(screen(t,q,r,c,rng,a.limit) for c in ordered for _ in range(3)):continue
            proofs=[]
            for c in ordered:
                e=exact(t,q,r,c,a.limit)
                if e is None:break
                proofs.append({'context':c,'cases':e})
            else:
                success.append({'remove':q,'representative':r,'proofs':proofs})
                print('FOUND',q,'->',r,flush=True)
    out={'table':a.table,'depth':a.depth,'limit':a.limit,'seconds':time.monotonic()-began,'screened':screened,'contexts':cs,'success':success}
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
    print('SUCCESS',len(success),'seconds',out['seconds'],flush=True)

if __name__=='__main__':main()
