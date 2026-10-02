#!/usr/bin/env python3
"""Exact physical-cover-three support and internal-witness assembly checks."""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib,json,random,time

PAIRS=[(0,1,2),(0,2,1),(1,2,0)]

def supports(arcs):
    out={(0,0)}
    for i,j in sorted(arcs):
        for s,t in list(out):
            if not ((s|t)&((1<<i)|(1<<j))):
                out.add((s|(1<<i),t|(1<<j)))
    return out

def weight(st,u,v):
    s,t=st;w=1
    for i in range(len(u)):
        if s>>i&1:w*=u[i]
        if t>>i&1:w*=v[i]
    return w

def check(n,arcs,u,v):
    arcs=set(arcs);ext={e for e in arcs if (e[0]<3)!=(e[1]<3)}
    full=supports(arcs);outside=supports(ext)
    bycore=[set()for _ in range(8)]
    for st in outside:bycore[(st[0]|st[1])&7].add(st)
    a=[sum(weight(st,u,v)for st in bycore[1<<i])for i in range(3)]
    b=[sum(weight(st,u,v)for st in bycore[(1<<i)|(1<<j)])for i,j,k in PAIRS]
    c=sum(weight(st,u,v)for st in bycore[7])
    Hset={st for st in full if st[0].bit_count()==2 and ((st[0]|st[1])&7)==7}
    H=sum(weight(st,u,v)for st in Hset)
    h=[];w=[];total_witnesses=Counter()
    for i,j,k in PAIRS:
        internal=[(i,j),(j,i)];counts=Counter();hh=0
        for p,q in internal:
            if (p,q)not in arcs:continue
            hh+=u[p]*v[q]
            for s,t in bycore[1<<k]:
                st=(s|(1<<p),t|(1<<q));counts[st]+=1
        assert all(m==1 for m in counts.values())
        assert set(counts)<=Hset
        total_witnesses.update(counts)
        ww=sum(weight(st,u,v)for st in counts)
        assert ww==hh*a[k] and ww<=H
        h.append(hh);w.append(ww)
    assert set(total_witnesses)==Hset
    assert all(m in [1,2]for m in total_witnesses.values())
    assert sum(w)<=2*H
    gamma=[sum(weight(st,u,v)for st in full if st[0].bit_count()==k)for k in range(4)]
    assert gamma==[1,sum(a)+sum(h),sum(b)+H,c]
    boundary=[b[0]*b[1]-a[0]*c,b[0]*b[2]-a[1]*c,b[1]*b[2]-a[2]*c]
    extensions=[a[k]*b[z]-c for z,(i,j,k)in enumerate(PAIRS)]
    assert all(x>=0 for x in boundary+extensions)
    order=sorted(range(3),key=lambda z:b[z],reverse=True)
    x,y,z=[b[i]for i in order];wx,wy,wz=[w[i]for i in order]
    major=(x-y)*(H-wx)+y*(2*H-sum(w))+(y-z)*wz
    assert major>=0
    rhs=(2*z+2*H-x-y)**2+3*(x-y)**2
    rhs+=12*sum(boundary)+12*sum(p*q for p,q in zip(h,extensions))+12*major
    assert rhs==4*(gamma[2]**2-3*gamma[1]*gamma[3])
    d=3
    while d and gamma[d]==0:d-=1
    for k in range(1,d):
        assert k*(d-k)*gamma[k]**2 >= (k+1)*(d-k+1)*gamma[k-1]*gamma[k+1]
    return d,len(Hset),sum(total_witnesses.values()),gamma

def main():
    start=time.monotonic();rng=random.Random(2368317)
    cases=zero=rankdrops=0;degrees=Counter();h_supports=witnesses=0
    # Every loopless relation on four vertices; C is the first three.
    potential=[(i,j)for i in range(4)for j in range(4)if i!=j]
    for mask in range(1<<len(potential)):
        arcs=[e for z,e in enumerate(potential)if mask>>z&1]
        u=[rng.randrange(4)for _ in range(4)];v=[rng.randrange(4)for _ in range(4)]
        d,hs,ws,g=check(4,arcs,u,v)
        cases+=1;degrees[d]+=1;zero+=int(0 in u+v);h_supports+=hs;witnesses+=ws
    # Every one of 64 internal directed core patterns, with 100 exterior data sets.
    internal=[(i,j)for i in range(3)for j in range(3)if i!=j]
    nonreal=None
    for core in range(64):
        for trial in range(100):
            n=6+trial%3
            arcs=[e for z,e in enumerate(internal)if core>>z&1]
            for i in range(3):
                for j in range(3,n):
                    state=rng.randrange(4)
                    if state&1:arcs.append((i,j))
                    if state&2:arcs.append((j,i))
            # Ensure an unweighted saturating matching; activities can still kill it.
            for i in range(3):arcs.append((i,3+i)if rng.randrange(2)else(3+i,i))
            low=0 if trial%2==0 else 1
            u=[rng.randrange(low,7)for _ in range(n)];v=[rng.randrange(low,7)for _ in range(n)]
            d,hs,ws,g=check(n,arcs,u,v)
            cases+=1;degrees[d]+=1;zero+=int(0 in u+v);rankdrops+=d<3
            h_supports+=hs;witnesses+=ws
            if d==3:
                a,b,c=g[3],g[2],g[1]
                disc=b*b*c*c-4*a*c**3-4*b**3-27*a*a+18*a*b*c
                if disc<0 and nonreal is None:
                    nonreal={'vertices':n,'arcs':sorted(set(arcs)),'u':u,'v':v,'gamma':g,'cubic_discriminant':disc}
    result={'verdict':'PASS','cases':cases,'exhaustive_four_vertex_relations':4096,
        'internal_patterns':64,'larger_cases_per_internal_pattern':100,
        'zero_activity_cases':zero,'larger_activity_rank_drops':rankdrops,
        'actual_degree_counts':dict(sorted(degrees.items())),
        'internal_support_instances':h_supports,'internal_witness_instances':witnesses,
        'exact_nonnegative_decomposition_verified':True,'first_nonreal_example':nonreal,
        'seed':2368317,'elapsed_seconds':time.monotonic()-start,
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('assembly_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
