"""Direct graph census from pairs of set partitions; standard library only."""
from itertools import permutations
from collections import Counter
from fractions import Fraction
from math import factorial, comb
from pathlib import Path
import json

def rgs(n):
    if n==0:
        yield (); return
    def rec(a,m):
        if len(a)==n: yield tuple(a); return
        for v in range(m+2): yield from rec(a+[v],max(m,v))
    yield from rec([0],0)

def canonical(p,q):
    k=max(p,default=-1)+1; l=max(q,default=-1)+1
    if k>l: p,q=q,p; k,l=l,k; flipped=True
    else: flipped=False
    M=[[0]*l for _ in range(k)]
    for i,j in zip(p,q): M[i][j]+=1
    cols=[tuple(M[i][j] for i in range(k)) for j in range(l)]
    can=min(tuple(sorted(tuple(c[i] for i in perm) for c in cols)) for perm in permutations(range(k)))
    return (k,l,flipped,can)

def statistics(key):
    k,l,flip,cols=key
    if not k: return 1,0,0,0
    mult=Counter(cols)
    auto=sum(Counter(tuple(c[i] for i in p) for c in cols)==mult for p in permutations(range(k)))
    for m in mult.values(): auto*=factorial(m)
    M=[[cols[j][i] for j in range(l)] for i in range(k)]
    row_leaves=Counter(tuple(row).index(1) for row in M if sum(row)==1)
    col_leaves=Counter(c.index(1) for c in cols if sum(c)==1)
    L=sum(comb(m,2) for m in row_leaves.values())+sum(comb(m,2) for m in col_leaves.values())
    parent=list(range(k+l))
    def find(x):
        while parent[x]!=x: x=parent[x]
        return x
    for i in range(k):
        for j in range(l):
            if M[i][j]: parent[find(i)]=find(k+j)
    components=Counter()
    for i in range(k):
        for j in range(l):
            components[find(i)]+=M[i][j]
    comps=list(components.values())
    return auto,L,len(comps),sum(x==1 for x in comps)

A=[1,1,4,10,33,91,298]
C=[0,1,3,6,17,40,125]
rows=[]; vertex_mass=[]; weighted_L=[]
for n in range(7):
    ps=list(rgs(n)); gs={canonical(p,q) for p in ps for q in ps}
    assert len(gs)==A[n],(n,len(gs),A[n])
    mass=Fraction(); lm=Fraction(); vm=Fraction(); conn=0;sym=0;bad=0;edge=0
    for key in gs:
        aut,L,ncomp,nedge=statistics(key)
        mass+=Fraction(1,aut);lm+=Fraction(L,aut);vm+=Fraction(key[0]+key[1]+2,2*aut)
        conn+=ncomp==1;sym+=aut>1;edge+=nedge>0
        if aut>1: assert 2*L<=aut
        exceptional=not(aut==1 or (aut==2 and L==1))
        bad+=exceptional
        residual=Fraction(aut-1-L,aut)
        assert residual>=0
        if exceptional: assert residual>=Fraction(1,6)
    assert conn==C[n],(n,conn,C[n])
    if n: assert edge==A[n-1]
    vertex_mass.append(vm);weighted_L.append(lm)
    if n>=2: assert lm==vertex_mass[n-2],(n,lm,vertex_mass[n-2])
    rows.append(dict(n=n,graphs=len(gs),connected=conn,symmetric=sym,exceptional=bad,isolated_edge=edge,weighted_mass=str(mass),leaf_weight=str(lm),residual=str(A[n]-mass-lm),Y=str(vm)))
result=dict(status='PASS',maximum_n=6,partition_pairs=sum(sum(1 for _ in rgs(n))**2 for n in range(7)),graphs_checked=sum(A),rows=rows,method='Direct partition-pair graph construction, canonical row-column relabeling, vertex automorphism enumeration, graph connectivity and exact rational identities.')
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
