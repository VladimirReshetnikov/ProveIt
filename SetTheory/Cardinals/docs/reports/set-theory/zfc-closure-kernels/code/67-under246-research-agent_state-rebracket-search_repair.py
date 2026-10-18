#!/usr/bin/env python3
"""Candidate search for the associative N74 rotation. No minimality claim."""
import sys,json,time,itertools,random
from pathlib import Path
if not __debug__:
    raise RuntimeError('Run with Python assertions enabled; do not use -O or -OO.')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'root_search'))
import compile_rebracket as compiler
BASE=compiler.BASE
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(BASE/'sources/prior'))
import review_affine_source as review
import prefix_affine as affine

def cases(n,r):
    for p,op,x in compiler.sites(n,r):
        v=review.PHYSICAL[x] if op in ('CI','CD') else x
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(v,zero) if op=='CD' else None
            extra=0;effect=None;overflow=False
            if op=='CI':nxt,overflow=review.full_inc(p);effect=('inc',v)
            elif op=='CD' and not zero:nxt,overflow=review.full_inc(p);effect=('dec',v);extra=1
            elif op=='CD':nxt,overflow=review.full_inc(review.full_strip(p,'0',1))
            elif op=='CB':nxt,overflow=review.full_inc(review.full_strip(p,'0',v))
            elif op=='CC':nxt=review.full_strip(p,'1',v)
            else:nxt=''
            right=[('b',int(c)) for c in nxt]+[('r',0,1,40+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))]
            yield (p,branch,affine.canon([('b',1)],right),op=='CH')

def run(table,c):
    _,steps=affine.run(table,*c[:3],halt=c[3],fuel=1500)
    assert steps>0

def base():
    n,r,t=compiler.load();n,r=compiler.mutate(n,r)
    t['178',0]=(0,'R','16');t['178',1]=(1,'R','206')
    t={k:v for k,v in t.items() if k[0]!='208'}
    return n,r,t,list(cases(n,r))

def main():
    start=time.monotonic();n,r,t,cc=base()
    states=sorted({q for q,b in t},key=int)
    critical=[1166]
    successes=[];tries=0;failcounts={}
    for w,d,q in itertools.product((0,1),('L','R'),states):
        a=(w,d,q);u=t.copy();u['218',0]=a;tries+=1
        try:
            for i in critical:run(u,cc[i])
            for i,c in enumerate(cc):run(u,c)
        except (AssertionError,KeyError) as e:
            failcounts[i]=failcounts.get(i,0)+1
            if i not in critical:critical.append(i)
        else:
            print('PASS',a,flush=True);successes.append(a)
    report=dict(scope='All single-row replacements of (218,0) in the 245-state rebracket candidate; inherited macro oracle; 1500 affine-rule fuel.',tries=tries,successes=successes,critical_cases=critical,failure_counts=failcounts,seconds=time.monotonic()-start)
    (HERE/'one_row_repair.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
