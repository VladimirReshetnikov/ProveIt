#!/usr/bin/env python3
"""Independent exact checks: stable-seed pendant extension and physical merge."""
from collections import defaultdict
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random,time
import sympy as sp

OUT=Path(__file__).resolve().parent
X=sp.Symbol('t')

def submasks(mask):
    s=mask
    while True:
        yield s
        if not s:return
        s=(s-1)&mask

def bits(mask):
    while mask:
        b=mask&-mask
        yield b.bit_length()-1
        mask^=b

def weight(S,T,u,v):
    out=1
    for i in bits(S):out*=u[i]
    for j in bits(T):out*=v[j]
    return out

def hall(S,T,adj):
    for R in submasks(S):
        neighbors=0
        for i in bits(R):neighbors|=adj[i]
        if (neighbors&T).bit_count()<R.bit_count():return False
    return True

def seed_bases(n,q,adj):
    # Tail elements occupy bits 0..n-1; private head dummies bits n..n+q-1.
    Q=(1<<q)-1
    out={}
    for T in range(1<<q):
        k=T.bit_count()
        for I in combinations(range(n),k):
            S=sum(1<<i for i in I)
            if hall(S,T,adj):out[S|((Q^T)<<n)]=(S,T)
    return out

def elementary_seed(n,q,adj):
    if q==0:return {0}
    Q=(1<<q)-1
    classes=[[1<<(n+j)] for j in range(q)]
    universals=[]
    for i in range(n):
        N=adj[i]&Q
        if not N:continue
        if N.bit_count()==1:
            classes[N.bit_length()-1].append(1<<i)
        else:
            assert N==Q
            universals.append([1<<i])
    classes+=universals
    out=set()
    for inds in combinations(range(len(classes)),q):
        for chosen in product(*(classes[i] for i in inds)):
            mask=sum(chosen)
            assert mask not in out
            out.add(mask)
    return out

def direct(n,adj,u,v):
    supports=set()
    witnesses=0
    def rec(remaining,S,T):
        nonlocal witnesses
        if not remaining:
            supports.add((S,T)); witnesses+=1; return
        i=(remaining&-remaining).bit_length()-1
        remaining^=1<<i
        rec(remaining,S,T)
        for j in bits(remaining):
            if adj[i]>>j&1:rec(remaining^(1<<j),S|(1<<i),T|(1<<j))
            if adj[j]>>i&1:rec(remaining^(1<<j),S|(1<<j),T|(1<<i))
    rec((1<<n)-1,0,0)
    mu=defaultdict(int)
    gamma=[0]*(n//2+1)
    for S,T in supports:
        k=S.bit_count(); w=weight(S,T,u,v)
        gamma[k]+=w
        mu[((1<<n)-1)^(S|T)]+=(-1)**k*w
    while len(gamma)>1 and gamma[-1]==0:gamma.pop()
    return {k:v for k,v in mu.items() if v},gamma,len(supports),witnesses

def operators(n,q,adj,u,v):
    B=seed_bases(n,q,adj)
    assert set(B)==elementary_seed(n,q,adj)
    mu={}
    tailfull=(1<<n)-1
    Q=(1<<q)-1
    for S,T in B.values():
        mask=(tailfull^S)|((Q^T)<<n)
        mu[mask]=(-1)**S.bit_count()*weight(S,T,u,v)
    mu={k:v for k,v in mu.items() if v}
    for j in range(q,n):
        parents=[i for i in range(n) if adj[i]>>j&1]
        assert len(parents)<=1
        out=defaultdict(int)
        for mask,c in mu.items():
            out[mask|(1<<(n+j))]+=c
            if parents and (mask>>parents[0]&1):
                i=parents[0]
                out[mask^(1<<i)]-=u[i]*v[j]*c
        mu={k:v for k,v in out.items() if v}
    out=defaultdict(int)
    for mask,c in mu.items():
        physical=0
        for i in range(n):
            a=(mask>>i)&1; b=(mask>>(n+i))&1
            if not(a or b):break
            if a and b:physical|=1<<i
        else:out[physical]+=c
    return {k:v for k,v in out.items() if v}

def exact_negative_roots(gamma):
    d=len(gamma)-1
    assert gamma[0]==1 and all(c>0 for c in gamma)
    if d<=1:return
    if d==2:
        assert gamma[1]**2>=4*gamma[0]*gamma[2]
        return
    P=sp.Poly.from_list(list(reversed(gamma)),X)
    intervals=P.intervals()
    assert sum(mult for (ab,mult) in intervals)==d,(gamma,intervals)
    assert all(ab[1]<=0 for (ab,mult) in intervals),(gamma,intervals)

def eval_poly(mu,values,derivative=0):
    out=0
    for mask,c in mu.items():
        if mask&derivative!=derivative:continue
        for i in bits(mask^derivative):c*=values[i]
        out+=c
    return out

def check_rayleigh(mu,n,rng):
    count=0
    for sample in range(3):
        vals=[rng.randrange(-4,5) for _ in range(n)]
        f=eval_poly(mu,vals)
        ds=[eval_poly(mu,vals,1<<i) for i in range(n)]
        for i,j in combinations(range(n),2):
            dij=eval_poly(mu,vals,(1<<i)|(1<<j))
            assert ds[i]*ds[j]-f*dij>=0
            count+=1
    return count

def check(n,q,adj,u,v,rng,rayleigh=False):
    mu,gamma,supports,witnesses=direct(n,adj,u,v)
    assert mu==operators(n,q,adj,u,v)
    assert mu[(1<<n)-1]==1
    assert all((n-mask.bit_count())%2==0 for mask in mu)
    exact_negative_roots(gamma)
    r=len(gamma)-1
    for k in range(1,r):
        assert k*(r-k)*gamma[k]**2 >= (k+1)*(r-k+1)*gamma[k-1]*gamma[k+1]
    rc=check_rayleigh(mu,n,rng) if rayleigh else 0
    return supports,witnesses,rc,r

def random_graph(n,q,rng):
    adj=[0]*n
    Q=(1<<q)-1
    for i in range(n):
        choices=[0]+[1<<j for j in range(q) if i!=j]
        if q>1 and i>=q:choices.append(Q)
        adj[i]=rng.choice(choices)
    for j in range(q,n):
        parent=rng.choice([-1]+[i for i in range(n) if i!=j])
        if parent>=0:adj[parent]|=1<<j
    return adj

def main():
    start=time.monotonic(); rng=random.Random(202610010933)
    cases=supports=witnesses=rayleigh=zero_cases=rank_drops=0
    # Every loopless 4-vertex relation with Q={0,1} and uncovered indegree <=1.
    n=4;q=2; edges=[(i,j) for i in range(n) for j in range(n) if i!=j]
    exhaustive=0
    for code in range(1<<len(edges)):
        adj=[0]*n
        for k,(i,j) in enumerate(edges):
            if code>>k&1:adj[i]|=1<<j
        if any(sum(bool(adj[i]>>j&1) for i in range(n))>1 for j in range(q,n)):continue
        u=[rng.randrange(4) for _ in range(n)];v=[rng.randrange(4) for _ in range(n)]
        a,b,c,r=check(n,q,adj,u,v,rng,rayleigh=True)
        cases+=1; exhaustive+=1; supports+=a; witnesses+=b;rayleigh+=c
        zero_cases+=0 in u+v
        unweighted=direct(n,adj,[1]*n,[1]*n)[1]
        rank_drops+=r<len(unweighted)-1
    suites=[]
    for n,q,count in [(3,0,80),(5,1,80),(6,3,200),(7,3,200),(8,4,200),(9,5,100)]:
        for trial in range(count):
            adj=random_graph(n,q,rng)
            u=[rng.randrange(5) for _ in range(n)];v=[rng.randrange(5) for _ in range(n)]
            a,b,c,r=check(n,q,adj,u,v,rng,rayleigh=True)
            cases+=1;supports+=a;witnesses+=b;rayleigh+=c
            zero_cases+=0 in u+v
            unweighted=direct(n,adj,[1]*n,[1]*n)[1]
            rank_drops+=r<len(unweighted)-1
        suites.append({'vertices':n,'Q_size':q,'cases':count})
    # Three universal tails: six full matching witnesses, exactly one full support.
    n=6;q=3;adj=[0,0,0,7,7,7]
    mu,gamma,ss,ww=direct(n,adj,[1]*n,[1]*n)
    assert gamma==[1,9,9,1] and ww>ss
    check(n,q,adj,[1]*n,[1]*n,rng,True)
    # Empty graph, empty physical vertex set, and all-zero activities.
    for n,q in [(0,0),(3,0),(3,3)]:
        check(n,q,[0]*n,[0]*n,[0]*n,rng,True)
    receipt={'verdict':'PASS','seed':202610010933,'weighted_cases':cases,
             'exhaustive_loopless_n4_Q2_relations':exhaustive,'random_suites':suites,
             'ordered_support_instances':supports,'matching_witness_instances':witnesses,
             'exact_Rayleigh_evaluation_checks':rayleigh,
             'cases_with_zero_activities':zero_cases,'cases_with_activity_induced_rank_drop':rank_drops,
             'checks':['Hall seed basis set equals elementary-symmetric class formula',
                       'direct physical support polynomial equals seed/pendant/merge operators',
                       'exact actual-degree negative real roots','exact actual-rank Newton inequalities',
                       'exact integer Rayleigh evaluations','unit empty coefficient'],
             'boundary_checks':['universal-tail witnesses counted once per support',
                       'q=0 and q=1','empty physical set','all-zero activities'],
             'elapsed_seconds':round(time.monotonic()-start,3)}
    (OUT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
