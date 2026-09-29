#!/usr/bin/env python3
"""Exact, independent finite checks for Cactus Rigidity for Matching Supports.
Python 3.10+; standard library only. Run from the package root.
No floating-point solver is used; these tests are not formal proofs.
"""
from __future__ import annotations
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import json
import platform
import time

ROOT = Path(__file__).resolve().parents[1]
# Coordinates in Z[zeta], zeta^2=zeta-1. Index j represents zeta^j.
UNITS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))

def mul(x, y):
    a,b=x; c,d=y
    return (a*c-b*d, a*d+b*c+b*d)

def norm(x):
    a,b=x
    return a*a+a*b+b*b

def graph(p, q, mask):
    return [(i,j) for i in range(p) for j in range(q) if mask >> (i*q+j) & 1]

def adjlist(p,q,edges):
    adj=[[] for _ in range(p+q)]
    for a,b in edges:
        adj[a].append(p+b); adj[p+b].append(a)
    return adj

def forest_chords(p,q,edges):
    parent=list(range(p+q))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    forest=[]; chords=[]
    for e in edges:
        a,b=e; x,y=find(a),find(p+b)
        if x==y: chords.append(e)
        else: parent[x]=y; forest.append(e)
    return forest,chords

def simple_cycles(adj):
    """Enumerate each simple undirected cycle once, by minimum vertex/orientation."""
    out=[]
    for start in range(len(adj)):
        def visit(path, used):
            v=path[-1]
            for w in adj[v]:
                if w==start:
                    if len(path)>=3 and path[1]<path[-1]: out.append(tuple(path))
                elif w>start and w not in used:
                    visit(path+[w], used|{w})
        visit([start], {start})
    return out

def cactus_info(p,q,edges):
    counts=Counter()
    cycles=simple_cycles(adjlist(p,q,edges))
    for cycle in cycles:
        for a,b in zip(cycle,cycle[1:]+cycle[:1]): counts[tuple(sorted((a,b)))]+=1
    return all(v<=1 for v in counts.values()), len(cycles)

def parity(perm):
    return sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))%2

def all_minors(p,q):
    for k in range(min(p,q)+1):
        for I in combinations(range(p),k):
            for J in combinations(range(q),k): yield I,J

def matching_supports(p,q,edges):
    """Covered-shore DP: merge different matchings covering the same vertex set."""
    neighbors=[[] for _ in range(p)]
    for a,b in edges: neighbors[a].append(b)
    states={(0,0)}
    for a in range(p):
        old=states.copy()
        for X,Y in old:
            for b in neighbors[a]:
                if not (Y>>b&1): states.add((X|(1<<a),Y|(1<<b)))
    return states

def ambiguity_constraints(p,q,edges,chords):
    support=set(edges); chord_index={e:i for i,e in enumerate(chords)}
    constraints=[]
    for I,J in all_minors(p,q):
        terms=[]
        for perm in permutations(range(len(J))):
            es=tuple((a,J[perm[i]]) for i,a in enumerate(I))
            if all(e in support for e in es):
                terms.append((parity(perm), tuple(chord_index[e] for e in es if e in chord_index)))
        if len(terms)>1: constraints.append(terms)
    constraints.sort(key=len)
    return constraints

def normalized_solutions(p,q,edges,modulus):
    _,chords=forest_chords(p,q,edges)
    constraints=ambiguity_constraints(p,q,edges,chords)
    count=0; trials=0; checked=0
    # Modulus 3 uses nonzero field entries 1,-1; modulus 6 uses sixth roots.
    base=2 if modulus==3 else 6
    for assignment in product(range(base), repeat=len(chords)):
        trials+=1
        valid=True
        for terms in constraints:
            checked+=1
            if modulus==3:
                value=sum((-1)**((sign+sum(assignment[t] for t in ids))%2) for sign,ids in terms)
                ok=(value%3)!=0
            else:
                a=b=0
                for sign,ids in terms:
                    x,y=UNITS[(3*sign+sum(assignment[t] for t in ids))%6]
                    a+=x; b+=y
                ok=norm((a,b))==1
            if not ok: valid=False; break
        count+=valid
    return count,trials,checked

def exact_det_phase(p,q,phases,I,J):
    a=b=0
    for perm in permutations(range(len(J))):
        es=[(row,J[perm[i]]) for i,row in enumerate(I)]
        if all(e in phases for e in es):
            v=(3*parity(perm)+sum(phases[e] for e in es))%6
            x,y=UNITS[v]; a+=x; b+=y
    return a,b

def cactus_phases(p,q,edges):
    forest,chords=forest_chords(p,q,edges)
    adj=adjlist(p,q,forest)
    phases={e:0 for e in edges}
    for a,b in chords:
        target=p+b; queue=deque([(a,0)]); seen={a}
        while queue:
            u,d=queue.popleft()
            if u==target:
                r=(d+1)//2
                phases[a,b]=(3*r+1)%6
                break
            for v in adj[u]:
                if v not in seen: seen.add(v); queue.append((v,d+1))
        else: raise AssertionError('Chord endpoints disconnected in spanning forest')
    return phases

def check_certificate(p,q,edges,phases):
    supports=matching_supports(p,q,edges)
    checks=0
    for I,J in all_minors(p,q):
        expected=(sum(1<<i for i in I),sum(1<<j for j in J)) in supports
        assert norm(exact_det_phase(p,q,phases,I,J))==int(expected), (p,q,edges,I,J)
        checks+=1
    return checks

def exhaustive(p,q,mode):
    hist=Counter(); assignments=checks=minor_checks=0
    for mask in range(1<<(p*q)):
        edges=graph(p,q,mask)
        is_cactus,cycle_count=cactus_info(p,q,edges)
        _,chords=forest_chords(p,q,edges)
        beta=len(chords)
        count,trials,tested=normalized_solutions(p,q,edges,mode)
        expected=(1 if mode==3 else 2**beta) if is_cactus else 0
        assert count==expected, (mode,p,q,mask,count,expected)
        if is_cactus:
            assert cycle_count==beta
            hist[beta]+=1
            minor_checks+=check_certificate(p,q,edges,cactus_phases(p,q,edges))
        assignments+=trials; checks+=tested
    return dict(shores=[p,q],graphs=1<<(p*q),cacti=sum(hist.values()),
                cacti_by_cycle_rank=dict(sorted(hist.items())),normalized_assignments=assignments,
                ambiguous_minor_evaluations=checks,canonical_cactus_minor_checks=minor_checks,
                all_passed=True)

# A small exact multivariate polynomial implementation, independent of any CAS.
NV=6
ZERO=(0,)*NV
class P:
    def __init__(self, data=0):
        self.d=({ZERO:Fraction(data)} if data else {}) if isinstance(data,(int,Fraction)) else {k:Fraction(v) for k,v in data.items() if v}
    def __add__(self, other):
        if not isinstance(other,P): other=P(other)
        d=self.d.copy()
        for m,c in other.d.items(): d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.d.items()})
    def __sub__(self,other): return self+-as_p(other)
    def __rsub__(self,other): return as_p(other)+-self
    def __mul__(self,other):
        other=as_p(other); d={}
        for m,c in self.d.items():
            for n,e in other.d.items():
                z=tuple(x+y for x,y in zip(m,n)); d[z]=d.get(z,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=P(1)
        for _ in range(n): out=out*self
        return out
    def diff(self,i):
        d={}
        for m,c in self.d.items():
            if m[i]:
                n=list(m); n[i]-=1; d[tuple(n)]=c*m[i]
        return P(d)
    def __eq__(self,other): return self.d==as_p(other).d

def as_p(x): return x if isinstance(x,P) else P(x)
def var(i):
    m=[0]*NV; m[i]=1; return P({tuple(m):1})
def phi_from_edges(p,q,edges,labels):
    out=P(0)
    for X,Y in matching_supports(p,q,edges):
        k=X.bit_count(); term=P((-1)**k)
        for a in range(p):
            if not X>>a&1: term=term*var(labels[a])
        for b in range(q):
            if not Y>>b&1: term=term*var(labels[p+b])
        out=out+term
    return out

def polynomial_checks():
    a,b,x,y,z,w=(var(i) for i in range(NV))
    f=a*b*x*y*z-(a+b)*(x*y+x*z+y*z)+(x+y+z)
    assert f==phi_from_edges(2,3,graph(2,3,63),list(range(5)))
    def ray(i,j): return f.diff(i)*f.diff(j)-f*f.diff(i).diff(j)
    U,V,W=x*y,x*z,y*z
    assert ray(0,1)==Fraction(1,2)*((U+V+W)**2+U**2+V**2+W**2)
    assert ray(2,3)==(1-Fraction(1,2)*(a+b)*z)**2+Fraction(1,4)*(3*a*a+2*a*b+3*b*b)*z*z
    assert ray(0,2)==(b*y*z-Fraction(1,2)*(y+z))**2+Fraction(1,4)*(3*y*y+2*y*z+3*z*z)
    # Independent leaf-support enumeration, all five attachment vertices.
    for v in range(5):
        if v<2:
            ed=graph(2,3,63)+[(v,3)]
            actual=phi_from_edges(2,4,ed,[0,1,2,3,4,5])
        else:
            ed=graph(2,3,63)+[(2,v-2)]
            actual=phi_from_edges(3,3,ed,[0,1,5,2,3,4])
        assert actual==w*f-f.diff(v)
    # Exact algebra in Q[sqrt(17)] confirms the claimed optimal K_2,3 defect.
    def qadd(a,b): return (a[0]+b[0],a[1]+b[1])
    def qscale(t,a): return (t*a[0],t*a[1])
    def qmul(a,b): return (a[0]*b[0]+17*a[1]*b[1], a[0]*b[1]+a[1]*b[0])
    c=(Fraction(-1,4),Fraction(1,4)); eps=(Fraction(-3,2),Fraction(1,2))
    assert qadd(qscale(2,c),(-1,0))==eps
    assert qadd((3,0),qscale(-4,qmul(c,c)))==eps
    return dict(rayleigh_identity_classes=3,rayleigh_pairs_covered=10,
                independently_enumerated_leaf_attachments=5,quadratic_field_identities=2,all_passed=True)

def theta(lengths):
    edges=[]; nxt=2
    for length in lengths:
        path=[0]+list(range(nxt,nxt+length-1))+[1]
        nxt+=length-1
        edges.extend(zip(path,path[1:]))
    adj=[[] for _ in range(nxt)]
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    color={0:0}; stack=[0]
    while stack:
        a=stack.pop()
        for b in adj[a]:
            if b not in color: color[b]=1-color[a]; stack.append(b)
            else: assert color[b]!=color[a]
    A=[v for v in range(nxt) if color[v]==0]; B=[v for v in range(nxt) if color[v]==1]
    ai={v:i for i,v in enumerate(A)}; bi={v:i for i,v in enumerate(B)}
    ed=[(ai[a],bi[b]) if color[a]==0 else (ai[b],bi[a]) for a,b in edges]
    return len(A),len(B),sorted(ed)

def compression_checks():
    count=0; cases=[]
    for lengths in [(2,2,4),(1,3,5),(3,3,5)]:
        p,q,edges=theta(lengths); edset=set(edges)
        degA=Counter(a for a,b in edges); degB=Counter(b for a,b in edges)
        choice=None
        for u,v in edges:
            if degA[u]==degB[v]==2:
                a=next(aa for aa,bb in edges if bb==v and aa!=u)
                b=next(bb for aa,bb in edges if aa==u and bb!=v)
                if (a,b) not in edset: choice=(a,v,u,b); break
        assert choice is not None
        a,v,u,b=choice
        phases={e:(i*i+2*i+1)%6 for i,e in enumerate(edges)}
        aa=[i for i in range(p) if i!=u]; bb=[j for j in range(q) if j!=v]
        aidx={t:i for i,t in enumerate(aa)}; bidx={t:i for i,t in enumerate(bb)}
        new={(aidx[i],bidx[j]):s for (i,j),s in phases.items() if i!=u and j!=v}
        new[aidx[a],bidx[b]]=(3+phases[a,v]+phases[u,b]-phases[u,v])%6
        oldsup=matching_supports(p,q,edges); newsup=matching_supports(p-1,q-1,list(new))
        for I,J in all_minors(p-1,q-1):
            oldI=tuple(sorted([aa[i] for i in I]+[u])); oldJ=tuple(sorted([bb[j] for j in J]+[v]))
            oldnorm=norm(exact_det_phase(p,q,phases,oldI,oldJ))
            newnorm=norm(exact_det_phase(p-1,q-1,new,I,J))
            assert oldnorm==newnorm
            x=(sum(1<<i for i in oldI),sum(1<<j for j in oldJ)) in oldsup
            y=(sum(1<<i for i in I),sum(1<<j for j in J)) in newsup
            assert x==y
            count+=1
        cases.append(list(lengths))
    return dict(theta_path_lengths=cases,augmented_minor_norm_and_support_pairs=count,all_passed=True)

def main():
    start=time.perf_counter()
    out={"status":"finite exact checks; not a proof-assistant verification",
         "python":platform.python_version(),"arithmetic":"integers, F_3, Z[zeta], rational polynomials, Q[sqrt(17)]"}
    out['sixth_root_exhaustive_3_by_3']=exhaustive(3,3,6)
    out['ternary_exhaustive_3_by_4']=exhaustive(3,4,3)
    out['core_checks']={}
    for name,lengths in [('E',(2,2,2)),('D',(1,3,3)),('T',(3,3,3))]:
        p,q,edges=theta(lengths)
        complex_count,complex_trials,_=normalized_solutions(p,q,edges,6)
        ternary_count,ternary_trials,_=normalized_solutions(p,q,edges,3)
        assert complex_count==ternary_count==0
        out['core_checks'][name]=dict(path_lengths=list(lengths),
            sixth_root_assignments=complex_trials,ternary_assignments=ternary_trials,
            faithful_sixth_root_assignments=0,support_exact_ternary_assignments=0)
    assert Fraction(13,10)-Fraction(12,25)+2*Fraction(13,30)**3==Fraction(13267,13500)<1
    out['polynomial_checks']=polynomial_checks()
    out['compression_checks']=compression_checks()
    out['elapsed_seconds']=round(time.perf_counter()-start,3)
    out['all_passed']=True
    dest=ROOT/'data'/'verification.json'; dest.parent.mkdir(exist_ok=True)
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
