#!/usr/bin/env python3
"""Independent finite representations; standard library only, safe under -O."""
from collections import defaultdict
from itertools import permutations
from math import comb, factorial
import hashlib,json,pathlib

ROOT=pathlib.Path(__file__).resolve().parent

def require(ok,msg):
    if not ok: raise RuntimeError(msg)

def logarithm_ode(N):
    t=[0,1]
    for n in range(1,N):
        v=sum(comb(n,j)*t[j+1] for j in range(n))+2*t[n]+1-(n==1)
        require(v%3==0,('noninteger log coefficient',n))
        t.append(v//3)
    a=[1]
    for n in range(1,N+1):
        a.append(sum(comb(n-1,j-1)*t[j]*a[n-j] for j in range(1,n+1)))
    return t,a

def insertion_tree(N):
    values=[1,1]; states={(2,1):1}
    for n in range(1,N):
        new=defaultdict(int)
        for (k,l),w in states.items():
            if l<=k:
                for j in range(1,l+1): new[k+1,j]+=w
                for j in range(l+1,k+1): new[j,j]+=w
                for j in range(k+1,n+2): new[k,j]+=w
            else:
                for j in range(1,k+1): new[k+1,j]+=w
                for j in range(k+1,l+1): new[k,j]+=w
        states=new; values.append(sum(states.values()))
    return values

def old_blocks(N):
    b=[0]*(N+1); b[1]=1
    c=[0,0]+[1]*(N-1)
    t=[b[i]+c[i] for i in range(N+1)]
    for k in range(1,N//2+1):
        b=[0,0]+[k*k*sum(comb(n-2,j)*b[j] for j in range(n-1)) for n in range(2,N+1)]
        c=[0,0]+[k*(k+1)*sum(comb(n-2,j)*c[j] for j in range(n-1)) for n in range(2,N+1)]
        t=[t[i]+b[i]+c[i] for i in range(N+1)]
    return t

def brute(n):
    return sum(not any(p[i]<p[i+1]<p[j]<p[j+1]
               for i in range(n-1) for j in range(i+2,n-1))
               for p in permutations(range(n)))

def excedance(n):
    return sum(all(p[i]>i for i in range(k)) and all(p[i]<=i for i in range(k,n))
               for p in permutations(range(n)) for k in range(n or 1))

def main():
    t,a=logarithm_ode(600)
    tree=insertion_tree(70)
    require(tree==a[:71],'insertion tree mismatch')
    require(old_blocks(70)==t[:71],'published block recurrence mismatch')
    bs=[]
    for n in range(9):
        v=brute(n); require(v==a[n],('brute mismatch',n)); bs.append(v)
    es=[]
    for n in range(9):
        v=excedance(n); require(v==t[n+1],('excedance mismatch',n)); es.append(v)
    oeis=[1,1,2,6,23,107,585,3669,25932,203768,1761109,16595757,
          169287873,1857903529,21823488238,273130320026,3627845694283,
          50962676849199,754814462534449,11754778469338581,
          191998054346198680]
    require(a[:len(oeis)]==oeis,'OEIS initial terms mismatch')
    data={'status':'pass','insertion_tree_terms':71,'block_log_terms':71,
          'brute_permutation_terms':bs,'brute_excedance_terms':es,
          'oeis_terms_checked':len(oeis),'ode_terms':601,
          'count_sha256':hashlib.sha256(json.dumps(a,separators=(',',':')).encode()).hexdigest(),
          'first_21_terms':a[:21]}
    (ROOT/'exact_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'counts_600.json').write_text(json.dumps(a,separators=(',',':'))+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__': main()
