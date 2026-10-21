#!/usr/bin/env python3
"""Independent finite base for the all-natural two-truth scheduler induction.
The infinite induction is stated separately in protected_tail_peer_review.md.
"""
from math import isqrt
import json

def tri(d):return d*(d+1)//2

def unpair(n):
    d=(isqrt(8*n+1)-1)//2
    e=n-tri(d)
    return d-e,e

def second(n):return unpair(n)[1]

def main():
    b=[];minimum=[];length=[];B=[];total=0;low=0
    for n in range(666):
        tag,y=unpair(n)
        if tag==0:delta,r=-1,y
        elif tag==1:delta,r=1,y
        elif tag==2:delta,r=0,second(y)
        else:delta,r=10,second(second(y))
        assert r==0 or r-1<n
        balance=delta+(b[r-1] if r else 0)
        mp=min(0,delta+(minimum[r-1] if r else 0))
        ll=1+(length[r-1] if r else 0)
        b.append(balance);minimum.append(mp);length.append(ll)
        low=min(low,total+mp);total+=balance;B.append(total)
        assert ll<=n+1
    assert low==-3 and min(B[6:])==7 and B[-1]==5762
    def p(t):return [0,-1,0,-2,-2,-2,-2][t] if t<7 else 7
    def q(t):
        d=(isqrt(8*t+1)-1)//2;e=t-tri(d)
        return sum(p(j)for j in range(d))+p(e)
    qs=[q(t)for t in range(45)]
    assert min(qs)==-11 and sum(x for x in qs if x<0)==-224
    assert sum(p(j)for j in range(9))==5
    A=0
    for k in range(26):
        r=second(second(k));mp=minimum[r-1]if r else 0
        assert A>=0 and A+10+mp>=0
        A+=10+(b[r-1]if r else 0)
    return {'status':'INDEPENDENT_FINITE_BASE_PASS','base_candidates':666,
            'minimum_global_prefix_balance':low,'minimum_B_from6':min(B[6:]),
            'B665':B[-1],'q_min':min(qs),'sum_negative_q':-224,
            'q_tail_lower_bound':3,'short_AX_cases':26,
            'scope':'Complete finite base and constants for the separate ordinary induction; no binary runtime claim.'}

if __name__=='__main__':print(json.dumps(main(),indent=2))
