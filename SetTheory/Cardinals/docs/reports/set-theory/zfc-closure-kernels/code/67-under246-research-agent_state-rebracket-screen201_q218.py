#!/usr/bin/env python3
"""Replay the two-guard q218/0 screen in the sparse 201-node compilation."""
import sys,json,itertools
from search_repair import HERE,cases,run
sys.path.insert(0,str(HERE.parents[1]/'root_search'))
import compile201

def main():
    n,r,t=compile201.build();t['243',0]=(0,'R','113');t['243',1]=(1,'R','218')
    cc=list(cases(n,r));critical=[1166,708];hist={};success=[]
    for w,d,q in itertools.product((0,1),('L','R'),sorted({q for q,b in t},key=int)):
        t['218',0]=(w,d,q)
        try:
            for i in critical:run(t,cc[i])
        except (AssertionError,KeyError):hist[i]=hist.get(i,0)+1
        else:success.append((w,d,q))
    report=dict(scope='201 source, q243 made pure N80, only q218/read0 changed; two specified affine cases, fuel1500.',critical=critical,histogram=hist,survivors=success)
    (HERE/'201_q218_screen.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
