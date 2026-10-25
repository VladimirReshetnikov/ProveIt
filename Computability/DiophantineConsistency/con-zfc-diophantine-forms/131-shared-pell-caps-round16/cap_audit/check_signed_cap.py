#!/usr/bin/env python3
"""Independent finite controls for signed-cap arithmetic, not an unbounded proof."""
from math import isqrt
import json
from pathlib import Path

def need(c,m):
    if not c: raise ValueError(m)

def pell(a,n):
    x,y=1,0
    for _ in range(n): x,y=a*x+(a*a-1)*y,x+a*y
    return x,y

def main():
    counts={'direct_pell_classification':0,'signed_residue_branches':0,'strong_cap_worst_case':0,'frame':0,'ternary':0}
    for a in range(2,18):
        canonical={pell(a,j)[1]:pell(a,j)[0] for j in range(20)}
        for y in range(5001):
            x=isqrt((a*a-1)*y*y+1)
            if x*x-(a*a-1)*y*y==1:
                need(canonical.get(y)==x,'noncanonical integral Pell pair')
                counts['direct_pell_classification']+=1
    for W in range(4,20):
        A=4*W**3+2
        need(4*W*((W-1)**2+1)<A-1,'pooled error bound')
        for k in range(-W+1,W):
            for j in range(W):
                x,y=pell(A,j)
                for sx in (-1,1):
                    for sy in (-1,1):
                        E=(sy*j-k)**2+(sx-1)**2
                        actual=(sy*y-k)**2+(sx*x-1)**2
                        need(actual%(A-1)==E%(A-1),'signed congruence mismatch')
                        need((E==0)==(sx==1 and sy*j==k),'sign/zero branch mismatch')
                        counts['signed_residue_branches']+=1
        V=pell(A,W)[1]
        for h in range((W-1)//2+1):
            yh=pell(A,h)[1]
            for m in range(1,W+1):
                need(V-W-1-m*yh*yh>=0,'linear aggregate completeness')
                counts['strong_cap_worst_case']+=1
    for a in range(-500,501):
        W=4+2*a*a
        need(W>4*abs(a),'square frame separation')
        counts['frame']+=1
    for G in range(2001):
        ok=False
        for w in range(isqrt(G)+1):
            r=G-w*(w+1)
            if r<0:break
            for u in range(isqrt(r)+1):
                v=isqrt(r-u*u)
                if u*u+v*v==r:ok=True;break
            if ok:break
        need(ok,'ternary finite representation')
        counts['ternary']+=1
    # Deliberately invalid controls demonstrate why both sign squares matter.
    A,W,k=4*4**3+2,4,1
    x,y=pell(A,k)
    need((y-k)**2%(A-1)==0 and -x!=x,'missing x orientation adversary')
    need((pell(3,3)[1]-1)%2==0,'missing modulus bound adversary')
    return {'status':'passed','counts':counts,'total_controls':sum(counts.values()),'scope':'finite regression only; unbounded proof in SIGNED_CAP_AUDIT.md','adversarial_controls':['negative x survives a y-only residue','a small modulus admits a wrong index']}

if __name__=='__main__':
    result=main(); out=Path(__file__).with_name('SIGNED_CAP_CHECK.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
