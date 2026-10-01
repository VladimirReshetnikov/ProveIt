#!/usr/bin/env python3
"""Independent exact support enumeration and leaf-compression regression checks.
No third-party dependencies. Feasible endpoint sets are stored as sets, so
multiple matchings of the same support are never counted more than once.
"""
from itertools import product
from random import Random
import json
from pathlib import Path

def coeffs(adj, u, v):
    m,n=len(u),len(v)
    wp=[1]*(1<<n)
    for j in range(1,1<<n):
        b=j&-j;wp[j]=wp[j-b]*v[b.bit_length()-1]
    out=[0]*(min(m,n)+1)
    for im in range(1<<m):
        reachable={0};uw=1
        for x in range(m):
            if not (im>>x)&1:continue
            uw*=u[x];new=set()
            for jm in reachable:
                for y in adj[x]:
                    if not (jm>>y)&1:new.add(jm|(1<<y))
            reachable=new
            if not reachable:break
        k=im.bit_count()
        if k<=min(m,n):out[k]+=uw*sum(wp[j] for j in reachable)
    while len(out)>1 and out[-1]==0:out.pop()
    return out

def ulc(a):
    r=len(a)-1
    return all(k*(r-k)*a[k]**2 >= (k+1)*(r-k+1)*a[k-1]*a[k+1]
               for k in range(1,r))

def compress(adj,u,v,b):
    # Cover is {left vertex 0} together with right vertices 0,...,b-1.
    outside=[j for j in range(b,len(v)) if j in adj[0]]
    newv=v[:b]+([sum(v[j] for j in outside)] if outside else [])
    newadj=[{j for j in row if j<b} for row in adj]
    if outside:newadj[0].add(b)
    return newadj,u[:],newv

def main():
    rng=Random(314159265)
    ntest=0;strict_rank=0
    for b in range(1,5):
      for _ in range(150):
        m=rng.randrange(2,7);outside=rng.randrange(1,5);n=b+outside
        adj=[]
        for x in range(m):
          adj.append({y for y in range(n if x==0 else b) if rng.randrange(2)})
        u=[rng.randrange(1,10) for _ in range(m)]
        v=[rng.randrange(1,10) for _ in range(n)]
        p=coeffs(adj,u,v)
        q=coeffs(*compress(adj,u,v,b))
        assert p==q,(adj,u,v,p,q)
        ntest+=1
        if len(p)-1==b+1:
          assert ulc(p),(adj,u,v,p)
          strict_rank+=1
    # Every 4 by 3 graph, with one fixed nonuniform integer external field.
    # This checks enumeration and the numerical consequences of the baseline.
    all_small=0
    for mask in range(1<<12):
      adj=[{j for j in range(3) if (mask>>(3*i+j))&1} for i in range(4)]
      p=coeffs(adj,[2,3,5,7],[11,13,17])
      assert ulc(p),(mask,p)
      all_small+=1
    # Exact coefficient formula and SOS ingredients for mixed rank-three graphs.
    mixed=0
    for _ in range(500):
      ls=[[rng.randrange(1,9) for _ in range(rng.randrange(4))] for __ in range(3)]
      leaves=[rng.randrange(1,9) for _ in range(rng.randrange(1,4))]
      a,b,c=map(sum,ls);d=sum(ls[2][i]*ls[2][j] for i in range(len(ls[2])) for j in range(i))
      h,y,z=[rng.randrange(1,9) for _ in range(3)];T=sum(leaves)
      eps,delta=rng.randrange(2),rng.randrange(2)
      A=a+c;B=b+c;q=a*b+a*c+b*c+d
      D=y*A+z*B;Q=y*z*q;C=eps*y+delta*z
      F=y*z*(eps*B+delta*A-eps*delta*c)
      p=[1,D+h*(C+T),Q+h*F+h*T*D,h*T*Q]
      while len(p)>1 and p[-1]==0:p.pop()
      adj=[({0} if eps else set())|({1} if delta else set())|set(range(2,2+len(leaves)))]
      u=[h]
      for weights,neigh in zip(ls,[{0},{1},{0,1}]):
        for w in weights:adj.append(neigh.copy());u.append(w)
      exact=coeffs(adj,u,[y,z]+leaves)
      assert p==exact
      assert D*D>=4*Q
      assert C*F*D-F*F-Q*C*C>=0
      assert ulc(p)
      mixed+=1
    result={"leaf_compression_graphs":ntest,"full_cover_rank_graphs":strict_rank,
            "exhaustive_4_by_3_graphs":all_small,"weighted_mixed_cover_formula_cases":mixed,
            "all_checks_passed":True,"random_seed":314159265,
            "meaning":"Exact regression evidence; the all-graph conclusions follow from the written proofs."}
    Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
