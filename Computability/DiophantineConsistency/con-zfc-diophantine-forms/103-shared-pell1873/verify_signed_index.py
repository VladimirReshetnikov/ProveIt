#!/usr/bin/env python3
"""Finite adversarial controls for signed Pell indices; not the universal proof."""
import json,math
from pathlib import Path

def check(t,msg):
    if not t:raise ValueError(msg)

def pell(a,n):
    d=a*a-1
    def mul(p,q):return p[0]*q[0]+d*p[1]*q[1],p[0]*q[1]+p[1]*q[0]
    out=(1,0);step=(a,1)
    while n:
        if n&1:out=mul(out,step)
        step=mul(step,step);n//=2
    return out

def norm(a,x,y):return x*x-(a*a-1)*y*y-1

def main():
    accepted=0; signs={str((e,d)):0 for e in (-1,1) for d in (-1,1)};cases=0
    for a in range(2,5):
        for i in range(1,4):
            X,Y=pell(a,i)
            for t in (1,2):
                n=i*Y*t;U,V=pell(a,n)
                check(V%(Y*Y)==0,'square-divisibility construction')
                x,y=1,0
                for h in range(4*n+1):
                    for e in (-1,1):
                        if (e*x-X)%U:continue
                        for d in (-1,1):
                            k=(d*h)%(4*Y)
                            if not 1<=k<=Y:continue
                            check(k==i,'signed-index false positive')
                            accepted+=1;signs[str((e,d))]+=1
                    x,y=(a*x+(a*a-1)*y)%U,(x+a*y)%U
                cases+=1
    # Essential negative control: omitting Y² | V admits a wrong index.
    a,i,n,h,k=2,3,6,9,9
    X,Y=pell(a,i);U,V=pell(a,n)
    q=((a-1)*pow(4*Y,-1,U))%U
    B=1+4*Y*q
    if B<2:B+=4*Y*U
    absS,R=pell(B,h);S=-absS
    check(0<k<=Y and U>=2 and B>=2,'negative-control domains')
    check(norm(a,X,Y)==norm(a,U,V)==norm(B,S,R)==0,'negative-control norms')
    check((B-a)%U==(B-1)%(4*Y)==(S-X)%U==(R-k)%(4*Y)==0,'negative-control congruences')
    check(V%(Y*Y)!=0 and k!=i,'missing divisibility really is essential')
    r={'status':'PASS','scope':'finite diagnostics only; universal proof is the review',
       'parameter_cases':cases,'accepted_signed_congruence_cases':accepted,'accepted_sign_counts':signs,
       'negative_control':{'omitted':'Y^2 divides abs(V)','A':a,'i':i,'n':n,'h':h,'k':k,'X':X,'Y':Y,'U':U,'V':V,'B':B,
                           'all_other_norms_and_congruences_pass':True,'wrong_index_admitted':True}}
    Path(__file__).with_name('SIGNED_INDEX_FINITE_CHECKS.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
