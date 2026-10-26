#!/usr/bin/env python3
"""Finite arithmetic corroboration; not a proof of the quantified theorem."""
import json, math

def need(c,s):
    if not c:raise ValueError(s)

def pell_mod(a,n,m):
    D=(a*a-1)%m
    def mul(u,v):return ((u[0]*v[0]+D*u[1]*v[1])%m,(u[0]*v[1]+u[1]*v[0])%m)
    out=(1%m,0);base=(a%m,1%m)
    while n:
        if n&1:out=mul(out,base)
        base=mul(base,base);n//=2
    return out

def frame_parameters(W,m):
    c,y=pell_mod(W+1,W,W*m)
    need(y%W==0,'divided ordinate is not integral')
    return c%m,(y//W)%m

def values(W,m):
    c,b=frame_parameters(W,m)
    out=[];xp=1%m;yp=0
    for k in range(m):
        out.append((b*yp)%m)
        xp,yp=(c*xp+(c*c-1)*yp)%m,(xp+c*yp)%m
    return out

def main():
    permutation_cases=0;digits=0;center_cases=0
    for p in (3,5,7,11,13):
        for a in (1,2,3):
            m=p**a
            for t in (1,2,3,5):
                W=p*p*t;c,b=frame_parameters(W,p**(a+1))
                need(b%p==1,'unit lemma')
                need(c%(p*p)==1,'abscissa congruence')
                vs=values(W,m)
                need(len(set(vs))==m,'Pell index permutation')
                permutation_cases+=1;digits+=m
    # The p^2 hypothesis protects the unit statement at p=3.
    c,b=frame_parameters(3,3)
    need(b==0,'negative control W=3 lost')
    params=[(3,3),(3,27),(5,125),(7,343),(15,675),(21,441),(35,1225),(105,315)]
    examples=[]
    for q,m in params:
        for W0 in (2,3,5,8):
            W=q*q*W0;K=W**3*(W+2)
            target=2*(q+1)*(K+2)%m
            roots=[d for d in range(m) if d*d%m==target]
            need(bool(roots),'center denominator lacks square root')
            d=roots[0];need(math.gcd(d,m)==1,'denominator root not a unit')
            r0=q*pow(d,-1,m)%m
            vs=values(W,m);k=vs.index(r0)
            if k%2==0:k+=m
            if k<=0:k+=2*m
            for kk in (k,k+2*m,k+4*m):
                L,y=pell_mod(W+1,W*kk,W*m)
                need(y%W==0,'quotient remainder')
                r=y//W
                need((L*L-K*r*r-1)%m==0,'frame norm')
                A=(L*L+2*r*r)%m
                need((2*A*(q+1)-(q+1)**2-1)%m==0,'common root')
                _,yp=pell_mod(W+1,W*kk,2*W)
                need(yp//W==1,'odd quotient')
            center_cases+=1
            examples.append({'q':q,'Omega':m,'W0':W0,'W':W,'k':k,'r_mod_Omega':r0})
    print(json.dumps({'permutation_cases':permutation_cases,'enumerated_index_classes':digits,'center_cases':center_cases,'cofinal_lifts_per_center':3,'negative_control_W3_passed':True,'examples':examples[:5],'scope':'finite corroboration; proof is RECYCLED_QUOTIENT_CENTER.md'},indent=2))

if __name__=='__main__':main()
