#!/usr/bin/env python3
"""Exact finite checks for the fixed-alphabet proof; not a proof by search."""
from pathlib import Path
from collections import Counter,deque
from math import gcd
import random,json,time,hashlib
P=Path(__file__).resolve().parent;rng=random.Random(431172026);start=time.time()
stats=Counter()

def elementary_cycles(rows,allowed):
    found=[];n=len(rows)
    for root in range(n):
        stack=[(root,(root,),1<<root)]
        while stack:
            v,path,seen=stack.pop()
            for w in rows[v]:
                if w==root:
                    if len(path) not in allowed:return None
                    found.append(path)
                elif w>root and not seen>>w&1:
                    stack.append((w,path+(w,),seen|1<<w))
    return found

def graph(n,j,k):
    shared=j+k-n
    a=list(range(shared))+list(range(shared,j))
    b=list(range(shared))+list(range(j,n))
    rows=[set() for _ in range(n)]
    for c in (a,b):
        for x,y in zip(c,c[1:]+c[:1]):rows[x].add(y)
    candidates=[(x,y) for x in range(n) for y in range(n) if x!=y and y not in rows[x]]
    rng.shuffle(candidates)
    for x,y in candidates:
        rows[x].add(y)
        if elementary_cycles(rows,{j,k}) is None:rows[x].remove(y)
    return rows,elementary_cycles(rows,{j,k})

def group(cycles,ell,z,n):
    rows=[set() for _ in range(n)];nodes=set()
    for c in cycles:
        if len(c)!=ell:continue
        nodes.update(c)
        for x,y in zip(c,c[1:]+c[:1]):rows[x].add(y)
    phase={z:0};queue=deque([z])
    while queue:
        u=queue.popleft()
        for v in rows[u]:
            want=(phase[u]+1)%ell
            if v in phase:assert phase[v]==want
            else:phase[v]=want;queue.append(v)
    assert set(phase)==nodes
    classes=[{v for v in nodes if phase[v]==a} for a in range(ell)]
    assert all(classes)
    singles={next(iter(c)) for c in classes if len(c)==1}
    assert len(singles)>=2*ell-len(nodes)
    return rows,nodes,phase,classes,singles

def factor_circulation(chosen,n):
    edges=Counter()
    for c in chosen:
        for x,y in zip(c,c[1:]+c[:1]):edges[x,y]+=1
    deg=[sum(v for (x,y),v in edges.items() if x==u) for u in range(n)]
    D=max(deg);regular=edges.copy()
    for u in range(n):regular[u,u]+=D-deg[u]
    decomposition=[]
    for step in range(D):
        mate={}
        def augment(u,seen):
            for v in range(n):
                if regular[u,v]<=0 or v in seen:continue
                seen.add(v)
                if v not in mate or augment(mate[v],seen):mate[v]=u;return True
            return False
        assert all(augment(u,set()) for u in range(n))
        successor={u:v for v,u in mate.items()}
        for u,v in successor.items():regular[u,v]-=1
        remaining=set(range(n));nonloops=[]
        while remaining:
            u=min(remaining);cyc=[];v=u
            while v in remaining:remaining.remove(v);cyc.append(v);v=successor[v]
            assert v==u
            if len(cyc)>1:nonloops.append(tuple(cyc))
        assert len(nonloops)<=1
        decomposition+=nonloops
    assert not any(regular.values())
    recovered=Counter()
    for c in decomposition:
        for x,y in zip(c,c[1:]+c[:1]):recovered[x,y]+=1
    assert recovered==edges
    assert len(decomposition)==len(chosen)
    assert Counter(map(len,decomposition))==Counter(map(len,chosen))
    return D

params=[(n,j,k) for n in range(6,15) for j in range(n//2+1,n) for k in range(j+1,n+1) if gcd(j,k)==1]
for trial in range(180):
    n,j,k=rng.choice(params);rows,cc=graph(n,j,k)
    js=[c for c in cc if len(c)==j];ks=[c for c in cc if len(c)==k]
    assert js and ks;stats['graphs']+=1
    for f in range(20):
        t=rng.randrange(2,min(j,8))
        chosen=[rng.choice(js),rng.choice(ks)]+[rng.choice(cc) for _ in range(t-2)]
        common=set(range(n))
        for c in chosen:common.intersection_update(c)
        assert common
        D=factor_circulation(chosen,n);assert D==t;stats['regularized_factorizations']+=1
        z=min(common)
        rj,Nj,pj,Cj,Sj=group(chosen,j,z,n)
        rk,Nk,pk,Ck,Sk=group(chosen,k,z,n)
        assert all(pk[v]-pj[v] in (0,k-j) for v in Nj&Nk)
        stats['phase_alignment_vertices']+=len(Nj&Nk)
        lost=(Sj&Nk)-Sk
        charged=[]
        for v in lost:
            alternatives=Ck[pk[v]]-{v}
            assert alternatives and not alternatives&Nj
            charged.append(min(alternatives))
        assert len(charged)==len(set(charged))
        stats['singleton_loss_injections']+=len(lost)
        assert common==Sj&Sk
        assert len(common)>=2*j+len(Nk)-2*len(Nj|Nk)>=2*j+k-2*n
        stats['mixed_families']+=1

for q in range(2,101):
    C=max(8,2*q-4)
    for n in range(2,2*q):
        assert 2*(n-1)**2+3<=n*n+C*n
        stats['small_state_constant_cases']+=1
    for s in range(2,251):
        for c in (1,s-1):
            assert (s-c)+2*s+c*c+C*c<=s*s+C*s
            stats['global_transfer_constant_cases']+=1

# Check exact interval-partition ranks for the two alphabet-class seed families.
for q in range(2,13):
    for trial in range(100):
        boundary=rng.randrange(1,q);N=rng.randrange(1,15)
        word=[rng.randrange(q) for _ in range(N)]
        cls=[int(a>=boundary) for a in word]
        expected=1+sum(a!=b for a,b in zip(cls,cls[1:]))
        dp=[0]+[N+1]*N
        for right in range(1,N+1):
            for left in range(right):
                if len(set(cls[left:right]))==1:dp[right]=min(dp[right],dp[left]+1)
        assert dp[N]==expected
        stats['two_class_lower_fragment_cases']+=1

out={'all_passed':True,'tests':dict(stats),'seconds':round(time.time()-start,3),
     'scope':'Finite structural and exact-arithmetic checks only; no exhaustive NFA census',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'article_sha256':hashlib.sha256((Path(__file__).resolve().parent.parent/'hamiltonian-rank.tex').read_bytes()).hexdigest()}
(P/'fixed_alphabet_lemmas_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
