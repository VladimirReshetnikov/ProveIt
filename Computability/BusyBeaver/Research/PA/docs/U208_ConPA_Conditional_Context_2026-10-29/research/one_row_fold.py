#!/usr/bin/env python3
"""Search one-row retargeting with a state alias under finite-history contexts."""
import argparse,itertools,json,random,time
from pathlib import Path
from context_alias import read,contexts

def screen(t,q,r,change,oldstate,c,rng,limit):
    cells={i:rng.randrange(2) for i in range(-limit-4,limit+5)};cells.update(c)
    b=cells[0];ow,od,oz=t[oldstate,b];target=r if oz==q else oz
    expected=dict(cells);expected[0]=ow
    actual=dict(cells);p=0;s=r
    for k in range(1,limit+1):
        if s==254:return False
        bit=actual[p]
        w,d,z=change[1] if (s,bit)==change[0] else t[s,bit]
        actual[p]=w;p+=d;s=r if z==q else z
        if (s,p)==(target,od) and actual==expected:return True
    return False

def exact(t,q,r,change,oldstate,context,limit):
    result=[]
    for oldbit in ([context[0]] if 0 in context else [0,1]):
        initial=dict(context);initial[0]=oldbit
        ow,od,oz=t[oldstate,oldbit];target=r if oz==q else oz
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
                    v=dict(values);v[p]=b;stack.append((s,p,dict(writes),v,list(trace)))
                continue
            w,d,z=change[1] if (s,bit)==change[0] else t[s,bit];z=r if z==q else z
            wn=dict(writes);wn[p]=w
            stack.append((z,p+d,wn,values,trace+[[s,p,bit,w,d,z]]))
            if len(stack)+len(cert)>16384:return None
        result.append({'oldbit':oldbit,'branches':cert})
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('--depth',type=int,default=7);p.add_argument('--limit',type=int,default=19);p.add_argument('--output',required=True);a=p.parse_args()
    began=time.monotonic();t=read(a.table);cs=contexts(t,a.depth)
    rng=random.Random(95163);states=sorted(cs);success=[];survivors=0;screened=0
    pairs=[(q,r,b) for q in states for r in states for b in [0,1] if q and r and q!=r and t[q,1-b]==t[r,1-b]]
    for i,(q,r,b) in enumerate(pairs):
        ordered=[(s,c) for s in [q,r] for c in sorted(cs[s],key=lambda c:(len(c),str(c)))]
        for w,d,z in itertools.product([0,1],[-1,1],states):
            if z==q:continue
            change=((r,b),(w,d,z));screened+=1
            if not all(screen(t,q,r,change,s,c,rng,a.limit) for s,c in ordered for _ in range(2)):continue
            survivors+=1
            proofs=[]
            for s,c in ordered:
                e=exact(t,q,r,change,s,c,a.limit)
                if e is None:break
                proofs.append({'oldstate':s,'context':c,'cases':e})
            else:
                success.append({'remove':q,'representative':r,'change':change,'proofs':proofs});print('FOUND',q,r,change,flush=True)
        if i%50==0:print('pairs',i,'/',len(pairs),flush=True)
    out={'table':a.table,'depth':a.depth,'limit':a.limit,'seconds':time.monotonic()-began,'screened':screened,'screen_survivors':survivors,'contexts':cs,'success':success}
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
    print('SUCCESS',len(success),'seconds',out['seconds'],flush=True)

if __name__=='__main__':main()
