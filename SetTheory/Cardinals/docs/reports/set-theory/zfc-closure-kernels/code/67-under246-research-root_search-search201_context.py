#!/usr/bin/env python3
"""Bounded counterexample-guided row search for the 201-node integration."""
import json, time
import repair201 as base
import compile_rebracket as c

review=c.module(c.BASE/'code/review_affine_source.py')
affine=c.module(c.BASE/'sources/prior/prefix_affine.py')

def cases(n,r):
    ans=[]
    for p,op,x in c.sites(n,r):
        v=review.PHYSICAL[x] if op in ('CI','CD') else x
        for z in ((True,False) if op=='CD' else (None,)):
            branch=(v,z) if op=='CD' else None
            extra=0;effect=None;overflow=False
            if op=='CI':nxt,overflow=review.full_inc(p);effect=('inc',v)
            elif op=='CD' and not z:nxt,overflow=review.full_inc(p);effect=('dec',v);extra=1
            elif op=='CD':nxt,overflow=review.full_inc(review.full_strip(p,'0',1))
            elif op=='CB':nxt,overflow=review.full_inc(review.full_strip(p,'0',v))
            elif op=='CC':nxt=review.full_strip(p,'1',v)
            else:nxt=''
            right=[('b',int(x)) for x in nxt]+[('r',0,1,40+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))]
            ans.append((p,branch,affine.canon([('b',1)],right),op=='CH'))
    return ans

def check(t,cse):
    p,branch,target,halt=cse
    try:
        _,literal=affine.run(t,p,branch,target,halt=halt,fuel=1500)
        return literal>0
    except (AssertionError,KeyError):return False

def run():
    n,r,t=base.build();cs=cases(n,r);states=sorted({q for q,b in t},key=int)
    witnesses=[3924];hist=[];survivors=[];began=time.monotonic()
    for target in states:
        for w in (0,1):
            for d in ('R','L'):
                t['244',1]=(w,d,target)
                failed=next((i for i in witnesses if not check(t,cs[i])),None)
                if failed is None:
                    failed=next((i for i,x in enumerate(cs) if not check(t,x)),None)
                    if failed is not None and failed not in witnesses:witnesses.append(failed);print('new witness',failed,flush=True)
                hist.append(dict(row=[w,d,target],failure=failed))
                if failed is None:
                    print('PASS',w,d,target,flush=True);survivors.append([w,d,target])
    out=dict(status='COMPLETE',scope='One-row substitutions at q244/read1; affine fuel1500; no new states; macro rows fixed.',candidates=len(hist),witnesses=witnesses,survivors=survivors,seconds=time.monotonic()-began,results=hist)
    (c.HERE/'search201_context_result.json').write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k!='results'},flush=True)

if __name__=='__main__':run()
