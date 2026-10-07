#!/usr/bin/env python3
"""Exact, offline checks for Report210. Python standard library only."""
import argparse
from collections import Counter, deque
from fractions import Fraction
from math import comb
from pathlib import Path
import json
import sys

GUARDS=0

def require(ok, message):
    global GUARDS
    GUARDS += 1
    if not ok:
        raise RuntimeError(message)

def bells(limit):
    values=[1]
    for n in range(limit):
        values.append(sum(comb(n,j)*values[j] for j in range(n+1)))
    return values

def kernel(k,n):
    require(1<=n<=k,'kernel domain')
    return Fraction(n*comb(2*k-n,k-n),2*k-n)

def good_partitions(n,B):
    require(n>=1,'P domain')
    return B[n]-(3**n+1+n*(n-1))//2+n*2**(n-1)

def good_pair(n,B):
    require(n>=1,'C domain')
    if n==1:
        return 0
    bad=1 if n==2 else 3**(n-2)-(n-2)*2**(n-3)
    return B[n-1]-bad

def formulas(k,B):
    require(k>=1,'positive half-length required')
    H=sum(kernel(k,n)*B[n] for n in range(1,k+1))
    T=sum(Fraction(k,n)*kernel(k,n)*B[n] for n in range(1,k+1))
    G=2*T-Fraction(4**k-comb(2*k,k),2)
    J=sum(k*comb(k-1,n+1)*(2*good_partitions(n,B)+(n-1)*good_pair(n,B))
          for n in range(1,k-1))
    E=sum(k*comb(k-1,n+1)*(2*B[n]+(n-1)*B[n-1]) for n in range(1,k-1))
    U=sum(comb(k-1,n+1)*(n*B[n]+comb(n,2)*B[n-1]) for n in range(1,k-1))
    require(all(v.denominator==1 for v in (H,T,G)),f'nonintegral at {k}')
    require(0<=E-J<=3*k**3*4**(k-1),f'exclusion error at {k}')
    require(G>=H>=0 and J>=0 and U>=0,f'negative/inclusion at {k}')
    return {'k':k,'H':int(H),'T':int(T),'G':int(G),'J':J,'combined':int(G)+J,
            'E_unrestricted_weighted':E,'U_unrestricted_rooted':U,
            'Bell':B[k],'next_Bell':B[k+1]}

def walks(k):
    adj=[[]]
    depth=[0]
    word=[0]
    def dfs(left,v):
        if depth[v]>left:
            return
        if left==0:
            if v==0:
                yield tuple(word)
            return
        for u in tuple(adj[v]):
            word.append(u)
            yield from dfs(left-1,u)
            word.pop()
        if len(adj)<=k and depth[v]+1<=left-1:
            u=len(adj)
            adj.append([v]);adj[v].append(u);depth.append(depth[v]+1);word.append(u)
            yield from dfs(left-1,u)
            word.pop();depth.pop();adj[v].pop();adj.pop()
    yield from dfs(2*k,0)

def normalize(word):
    labels={}
    return tuple(labels.setdefault(v,len(labels)) for v in word)

def rotate(word,step=1):
    core=word[:-1]
    step%=len(core)
    moved=core[step:]+core[:step]
    return normalize(moved+(moved[0],))

def distances(adj,root):
    depth=[None]*len(adj);depth[root]=0;q=deque([root])
    while q:
        a=q.popleft()
        for b in adj[a]:
            if depth[b] is None:
                depth[b]=depth[a]+1;q.append(b)
    return depth

def metadata(w):
    edges=Counter(tuple(sorted(pair)) for pair in zip(w,w[1:]))
    adj=[[] for _ in range(max(w)+1)]
    for a,b in edges:
        adj[a].append(b);adj[b].append(a)
    repeated=[e for e,m in edges.items() if m>2]
    common=set(range(len(adj)))
    repdegree=Counter()
    for edge in repeated:
        common.intersection_update(edge);repdegree.update(edge)
    isG=bool(common)
    isH=all(0 in edge for edge in repeated)
    isJ=False
    hubs=[v for v,d in repdegree.items() if d>=3]
    if len(hubs)==1:
        depth=distances(adj,hubs[0])
        distal=[m for (a,b),m in edges.items() if min(depth[a],depth[b])==1]
        isJ=max(depth)<=2 and distal.count(4)==1 and all(m in (2,4) for m in distal)
    depth=distances(adj,0)
    distal=[m for (a,b),m in edges.items() if min(depth[a],depth[b])==1]
    isU=max(depth)<=2 and distal.count(4)==1 and all(m in (2,4) for m in distal)
    n=w[:-1].count(0)
    return isG,isH,isJ,isU,n

def partitions(n):
    word=[0]
    def visit(maximum):
        if len(word)==n:
            yield tuple(word)
            return
        for a in range(maximum+2):
            word.append(a)
            yield from visit(max(maximum,a))
            word.pop()
    if n==0:
        yield ()
    else:
        yield from visit(0)

def check_partitions(B):
    rows=[]
    for n in range(1,11):
        total=p=c=0
        for pi in partitions(n):
            total+=1
            if sum(v>=2 for v in Counter(pi).values())>=3:
                p+=1
                if n>=2 and pi[0]==pi[1]:
                    c+=1
        require(total==B[n],f'partition total {n}')
        require(p==good_partitions(n,B),f'partition restriction {n}')
        require(c==good_pair(n,B),f'specified pair {n}')
        rows.append({'n':n,'Bell':total,'P':p,'C_good':c})
    return rows

def check_catalan():
    K=32
    C=[comb(2*j,j)//(j+1) for j in range(K+1)]
    coeff=[1]+[0]*K
    checks=0
    for n in range(1,K+1):
        coeff=[sum(coeff[j]*C[d-j] for j in range(d+1)) for d in range(K+1)]
        for k in range(n,K+1):
            require(coeff[k-n]==kernel(k,n),f'Catalan convolution {k},{n}')
            checks+=1
    return checks

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('data/exact_checks.json'))
    ap.add_argument('--self-test-failure',action='store_true')
    args=ap.parse_args()
    if args.self_test_failure:
        require(False,'intentional failure: guards are active')
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    B=bells(513)
    partition_rows=check_partitions(B)
    catalan_checks=check_catalan()
    reference=[1,3,12,57,303,1747,10727,69331]
    exhaustive=[]
    for k in range(1,9):
        counts=Counter();D=Counter();seen=set()
        for w in walks(k):
            require(w not in seen,f'duplicate canonical walk {k}')
            seen.add(w)
            g,h,j,u,n=metadata(w)
            require(not(g and j),f'family overlap {k}')
            require(not h or g,f'root family inclusion {k}')
            r=rotate(w)
            require(rotate(r,-1)==w,f'rotation inverse {k}')
            rg,rh,rj,ru,rn=metadata(r)
            require((rg,rj)==(g,j),f'rotation invariance {k}')
            counts['M']+=1;counts['G']+=g;counts['H']+=h;counts['J']+=j;counts['U']+=u
            if u:
                D[n]+=1
        f=formulas(k,B)
        require(counts['M']==reference[k-1],f'OEIS count {k}')
        for key in ('G','H','J'):
            require(counts[key]==f[key],f'geometric formula {k},{key}')
        require(counts['U']==f['U_unrestricted_rooted'],f'rooted total {k}')
        for n in range(1,k+1):
            s=k-n
            expected=comb(k-1,s-2)*(n*B[n]+comb(n,2)*B[n-1]) if s>=2 else 0
            require(D[n]==expected,f'rooted secondary count {k},{n}')
        require(f['combined']<=counts['M'],f'lower envelope {k}')
        exhaustive.append({'k':k,**dict(counts),'rooted_secondary_by_n':dict(sorted(D.items()))})
        print(f'exhaustive k={k}: '+json.dumps(dict(counts),sort_keys=True),flush=True)
    scalar_checks=0
    for k in range(2,25):
        for m in range(1,20):
            value=sum(k*comb(k-1,n+1)*(2*m**n+(n-1)*m**(n-1)) for n in range(1,k-1))
            rhs=Fraction(k,m*m)*((m+1)**(k-2)*(2*m*m+(k-1)*m-2)+2+(k-3)*m-2*(k-1)*m*m)
            require(value==rhs,f'scalar binomial identity {k},{m}')
            scalar_checks+=1
    rows=[formulas(k,B) for k in range(1,33)]
    large=[formulas(k,B) for k in (16,32,64,128,256,512)]
    for k in range(1,33):
        d=[(n,Fraction(k,n)*kernel(k,n)) for n in range(1,k+1)]
        require(sum(v*2**n for n,v in d)==Fraction(4**k,2),f'exception 2 {k}')
        require(sum(v for n,v in d)==Fraction(comb(2*k,k),2),f'exception 1 {k}')
        require(sum(v*n for n,v in d)==k*comb(2*k,k)//(k+1),f'exception n {k}')
    require(rows[7]['J']==360 and all(r['J']==0 for r in rows[:7]),'first secondary term')
    require(rows[15]['combined']==330838666521,'k16 lower-envelope regression')
    result={'status':'passed','scope':'Finite exact corroboration; all-k and limit statements use the report proofs.',
            'exhaustive_max_k':8,'partition_max_n':10,'catalan_max_k':32,
            'catalan_coefficient_checks':catalan_checks,'scalar_identity_checks':scalar_checks,
            'scalar_k_range':[2,24],'scalar_m_range':[1,19],
            'exhaustive':exhaustive,'partition_checks':partition_rows,'exact_rows':rows,
            'selected_large_exact_rows':large,'explicit_guard_calls':GUARDS}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(f'PASS: {GUARDS} explicit guards; no floating-point checks',flush=True)

if __name__=='__main__':
    main()
