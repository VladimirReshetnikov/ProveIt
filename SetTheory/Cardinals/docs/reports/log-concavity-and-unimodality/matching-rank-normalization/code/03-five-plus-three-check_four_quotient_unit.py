from itertools import combinations,combinations_with_replacement
import json,time

def rank(seq):
    bs={}
    for u in seq:
        while u:
            b=u.bit_length()-1
            if b in bs:u ^=bs[b]
            else:bs[b]=u;break
    return len(bs)

B=[1,2,4,8]
checks=0;minimum=None;zeros=0
for last in range(16):
    E=B+([last] if last else [])
    eb={i:list(combinations(E,i)) for i in range(1,5)}
    V=sum(rank(b)==4 for b in eb[4])
    for K in combinations_with_replacement(range(16),3):
        X=sum(rank((v,)+es)==4 for v in K for es in eb[3])
        N=sum(rank(vs+es)==4 for vs in combinations(K,2) for es in eb[2])
        Z=sum(rank(K+es)==4 for es in eb[1])
        W=sum(rank(K+es)==4 and rank(es)==2 for es in eb[2])
        # A qualifying pair must leave a rank-two core quotient, so rank(K+es)=4.
        slack=V+X-N-Z+2*W
        checks+=1
        if minimum is None or slack<minimum:
            minimum=slack;arg=(last,K,V,X,N,Z,W)
        if slack==0:zeros+=1
        if slack<0:raise RuntimeError((last,K,V,X,N,Z,W,slack))
print(json.dumps(dict(checks=checks,minimum=minimum,arg=arg,zeros=zeros),indent=2))
