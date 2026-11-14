#!/usr/bin/env python3
"""Allow positive blocks on both sides of a contextual state alias."""
import argparse,json,random,time
from pathlib import Path
from context_alias import read,contexts

def screen(t,q,r,c,rng,limit):
    initial={i:rng.randrange(2) for i in range(-limit-4,limit+5)}
    initial.update(c)
    old=dict(initial);new=dict(initial);os=q;ns=r;op=np=0
    oh={};nh={}
    for k in range(1,limit+1):
        if os!=254:
            w,d,z=t[os,old[op]];old[op]=w;op+=d;os=z
            s=r if os==q else os
            key=(s,op)
            for tape in nh.get(key,[]):
                if tape==old:return True
            oh.setdefault(key,[]).append(dict(old))
        if ns!=254:
            w,d,z=t[ns,new[np]];new[np]=w;np+=d;ns=r if z==q else z
            key=(ns,np)
            for tape in oh.get(key,[]):
                if tape==new:return True
            nh.setdefault(key,[]).append(dict(new))
        if os==ns==254:return True
    return False

def equivalent(old,new,values,q,r):
    os,op,ow,ot=old;ns,np,nw,nt=new
    if not ot or not nt:return False
    if os==ns==254:return True
    if ((r if os==q else os),op)!=(ns,np):return False
    return all(ow.get(x,values.get(x,('v',x)))==nw.get(x,values.get(x,('v',x))) for x in set(ow)|set(nw))

def exact(t,q,r,context,limit):
    # alternate old and new steps; compare against all positive opposite prefixes
    stack=[([(q,0,{},[])],[(r,0,{},[])],dict(context),0)]
    cert=[]
    while stack:
        oh,nh,values,turn=stack.pop()
        found=None
        for old in (oh[-1:] if turn==1 else oh[1:]):
            for new in (nh[1:] if turn==1 else nh[-1:]):
                if equivalent(old,new,values,q,r):found=(old,new);break
            if found:break
        if found:
            cert.append({'initial':values,'old_trace':found[0][3],'new_trace':found[1][3]});continue
        if len(oh)>limit and len(nh)>limit:return None
        h=oh if turn==0 else nh
        s,p,writes,trace=h[-1]
        if s==254:
            if len(oh)>limit or len(nh)>limit:return None
            stack.append((oh,nh,values,1-turn));continue
        bit=writes.get(p,values.get(p))
        if bit is None:
            for b in (0,1):
                nv=dict(values);nv[p]=b;stack.append((oh,nh,nv,turn))
            continue
        w,d,z=t[s,bit]
        if turn==1 and z==q:z=r
        nw=dict(writes);nw[p]=w
        history=h+[(z,p+d,nw,trace+[[s,p,bit,w,d,z]])]
        stack.append((history if turn==0 else oh,history if turn==1 else nh,values,1-turn))
        if len(stack)+len(cert)>16384:return None
    return cert

def main():
    p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('--depth',type=int,default=5);p.add_argument('--limit',type=int,default=19);p.add_argument('--output',required=True);a=p.parse_args()
    began=time.monotonic();t=read(a.table);cs=contexts(t,a.depth)
    rng=random.Random(2347618);states=sorted(cs);success=[];survivors=0
    for q in states:
        if q==0:continue
        if not cs[q]:print('UNREACHABLE',q,flush=True);continue
        ordered=sorted(cs[q],key=lambda c:(len(c),str(c)))
        for r in states:
            if r==q:continue
            if not all(screen(t,q,r,c,rng,a.limit) for c in ordered for _ in range(3)):continue
            survivors+=1; print('SCREEN',q,r,flush=True)
            proofs=[]
            for c in ordered:
                e=exact(t,q,r,c,a.limit)
                if e is None:break
                proofs.append({'context':c,'cases':e})
            else:
                success.append({'remove':q,'representative':r,'proofs':proofs})
                print('FOUND',q,'->',r,flush=True)
    out={'table':a.table,'depth':a.depth,'limit':a.limit,'seconds':time.monotonic()-began,'screen_survivors':survivors,'contexts':cs,'success':success}
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
    print('SUCCESS',len(success),'seconds',out['seconds'],flush=True)

if __name__=='__main__':main()
