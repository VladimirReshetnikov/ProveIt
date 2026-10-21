#!/usr/bin/env python3
"""Independent full MP finite regression for the concrete quotient splice."""
from pathlib import Path
import argparse,json,sys,itertools,hashlib
from math import isqrt
def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();import source_language as s
    tree=s.tree(json.loads(a.source.read_text()));mp=s.subtree(tree,'110100101');rows=s.sites((mp,('CH',None)));g=s.graph_intervals(rows);assert g==s.graph_arithmetic(rows)[0]
    P=lambda x,y:(x+y)*(x+y+1)//2+y
    def run(rr):
        rr=rr[:];pc=0
        for tick in range(2000000):
            _,op,r=rows[pc];to=g[pc][1]
            if op=='CH':return rr,tick
            if op=='CI':rr[r]+=1;pc=to[0]
            elif op=='CD':b=int(rr[r]>0);rr[r]-=b;pc=to[b]
            else:pc=to[0]
        raise RuntimeError('finite step cap')
    count=0;maxsteps=0;success=0
    for t,w,d,x,tail in itertools.product(range(4),range(4),range(3),range(4),range(3)):
        y=d+x;p=P(t,y)
        hs=sorted({0,1,2,3,*(4*p+r for r in range(4)),4*p+4,max(0,4*p-1)})
        for h in hs:
            inp=[11,t,w,7,d,h,0,0,P(x,tail)];out,ticks=run(inp)
            ok=h//4==p;expected=[11,y if ok else 0,P(0,w)if ok else w,7,y,0,0,0,tail]
            assert out==expected,(inp,out,expected)
            count+=1;success+=ok;maxsteps=max(maxsteps,ticks)
    result=dict(source_sha256=hashlib.sha256(a.source.read_bytes()).hexdigest(),status='FINITE_FULL_MP_CONTRACT_PASS',cases=count,successful_cases=success,maxsteps=maxsteps,scope='Finite regression only; mathematical all-natural loop proof and logical soundness are separate obligations.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
