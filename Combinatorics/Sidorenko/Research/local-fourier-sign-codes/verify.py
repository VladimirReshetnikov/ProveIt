#!/usr/bin/env python3
"""Exact, standard-library checks accompanying Local Fourier Sign Codes.

Run: python3 verify.py --output verification_results.json
These finite checks complement, and do not replace, the proofs in article.tex.
No numerical tolerance or floating-point arithmetic is used in any assertion.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from fractions import Fraction as F
from itertools import product, combinations
from math import comb, prod
from pathlib import Path
import json
import random

FACES = [
    (0,1,3),(0,1,9),(0,2,3),(0,2,9),(1,3,10),(1,7,10),
    (1,7,12),(1,9,12),(2,3,4),(2,4,9),(3,4,11),(3,10,11),
    (4,8,9),(4,8,11),(5,6,7),(5,6,11),(5,7,10),(5,10,11),
    (6,7,12),(6,8,11),(6,8,12),(8,9,12)]

class Group:
    def __init__(self, moduli: tuple[int, ...]):
        if not moduli or any(m < 2 for m in moduli):
            raise ValueError("Group moduli must be at least two.")
        self.moduli = moduli
        self.elements = list(product(*(range(m) for m in moduli)))
        self.n = len(self.elements)
        index = {x: i for i, x in enumerate(self.elements)}
        self.add = [[index[tuple((a+b) % m for a,b,m in zip(x,y,moduli))]
                     for y in self.elements] for x in self.elements]
        self.neg = [index[tuple(-a % m for a,m in zip(x,moduli))]
                    for x in self.elements]
        self.is_boolean = all(m == 2 for m in moduli)
    def sum(self, xs):
        s = 0
        for x in xs:
            s = self.add[s][x]
        return s
    def character(self, xi: int, x: int) -> int:
        if not self.is_boolean:
            raise ValueError("Only Boolean characters are evaluated in primal checks.")
        return (-1) ** (sum(a*b for a,b in zip(self.elements[xi],self.elements[x])) % 2)


def graph(n, edges):
    edges = tuple(tuple(sorted(e)) for e in edges)
    assert len(set(edges)) == len(edges) and all(u != v for u,v in edges)
    adj = [[] for _ in range(n)]
    for k,(u,v) in enumerate(edges):
        adj[u].append((v,k)); adj[v].append((u,k))
    colors = [None] * n
    parents = [None] * n
    order = []
    roots = []
    tree = set()
    for r in range(n):
        if colors[r] is not None:
            continue
        roots.append(r); colors[r] = 0
        q = deque([r])
        while q:
            v = q.popleft(); order.append(v)
            for u,k in adj[v]:
                if colors[u] is None:
                    colors[u] = 1-colors[v]; parents[u] = (v,k)
                    tree.add(k); q.append(u)
                else:
                    assert colors[u] != colors[v], "Graph is not bipartite."
    return dict(n=n, edges=edges, adj=adj, colors=colors, parents=parents,
                order=order, roots=roots, chords=[k for k in range(len(edges)) if k not in tree])


def flow_values(h, g):
    """Enumerate each conserved edge labeling once, via chords of a forest."""
    m = len(h['edges'])
    for chord_labels in product(range(g.n), repeat=len(h['chords'])):
        labels = [0] * m
        balance = [0] * h['n']
        for k,xi in zip(h['chords'], chord_labels):
            labels[k] = xi
            u,v = h['edges'][k]
            balance[u] = g.add[balance[u]][xi]
            balance[v] = g.add[balance[v]][xi]
        for v in reversed(h['order']):
            parent = h['parents'][v]
            if parent is not None:
                u,k = parent
                xi = g.neg[balance[v]]
                labels[k] = xi
                balance[u] = g.add[balance[u]][xi]
                balance[v] = g.add[balance[v]][xi]
        assert all(balance[r] == 0 for r in h['roots'])
        assert all(g.sum(labels[k] for _,k in h['adj'][v]) == 0 for v in range(h['n']))
        yield tuple(labels)


def cycle_counts(h):
    """Exact simple-cycle inventory; intended for the small test graphs."""
    out = Counter()
    m = len(h['edges'])
    for mask in range(1, 1 << m):
        selected = [h['edges'][k] for k in range(m) if mask >> k & 1]
        if len(selected) < 4:
            continue
        adj = {}
        for u,v in selected:
            adj.setdefault(u, []).append(v); adj.setdefault(v, []).append(u)
        if any(len(ns) != 2 for ns in adj.values()):
            continue
        seen = {next(iter(adj))}; todo = list(seen)
        while todo:
            v = todo.pop()
            for u in adj[v]:
                if u not in seen:
                    seen.add(u); todo.append(u)
        if len(seen) == len(adj):
            out[len(selected)] += 1
    return dict(sorted(out.items()))


def fourier_boolean(g, values):
    return [sum((values[x]*g.character(xi,x) for x in range(g.n)), F(0))/g.n
            for xi in range(g.n)]


def primal_density(h, g, values):
    # Fix one root of each connected component by translation invariance.
    free = [v for v in range(h['n']) if v not in h['roots']]
    total = F(0)
    for xs in product(range(g.n), repeat=len(free)):
        labels = [0] * h['n']
        for v,x in zip(free,xs): labels[v] = x
        total += prod(values[g.add[labels[u]][g.neg[labels[v]]]] for u,v in h['edges'])
    return total/(g.n**len(free))


def moments(g, coeff, d):
    M = F(0); S = F(0); D = F(0)
    for xs in product(range(g.n), repeat=d):
        if g.sum(xs) != 0:
            continue
        a = prod((coeff[x] for x in xs), start=F(1))
        M += abs(a); S += a
        if a < 0: D -= a
    assert M-S == 2*D
    return M,S,D


def binary_rank(vectors):
    pivots = {}
    for x in vectors:
        while x:
            k = x.bit_length()-1
            if k in pivots: x ^= pivots[k]
            else:
                pivots[k] = x
                break
    return len(pivots)


def relation_masks(g, support, D):
    reps = []
    rep_for = {}
    for xi in support:
        if xi not in rep_for:
            j = len(reps); reps.append(xi)
            rep_for[xi] = j; rep_for[g.neg[xi]] = j
    masks = set()
    for k in range(1,D+1):
        for xs in product(support, repeat=k):
            if g.sum(xs) == 0:
                mask = 0
                for xi in xs: mask ^= 1 << rep_for[xi]
                masks.add(mask)
    return reps, masks


def shortest_negative_relation(g, support, sign_bits):
    """BFS in the two-sheeted Cayley cover; return a shortest witness or None."""
    start=(0,0); target=(0,1)
    parent={start:None}; todo=deque([start])
    while todo:
        state=todo.popleft()
        for xi in support:
            nxt=(g.add[state[0]][xi],state[1]^sign_bits[xi])
            if nxt in parent: continue
            parent[nxt]=(state,xi)
            if nxt==target:
                word=[]; cur=nxt
                while parent[cur] is not None:
                    prev,step=parent[cur]; word.append(step); cur=prev
                word.reverse()
                return word
            todo.append(nxt)
    return None


def check_shortest_relations():
    out=[]
    for mods,support,bits,expected in [
        ((3,),[1,2],{1:1,2:1},3),
        ((5,),[1,4],{1:1,4:1},5),
        ((7,),[1,6],{1:1,6:1},7),
        ((2,2),[1,2,3],{1:1,2:0,3:0},3),
        ((2,2,2),[1,2,4,7],{1:1,2:0,4:0,7:0},4),
        ((2,2),[1,2,3],{1:1,2:0,3:1},None)]:
        g=Group(mods)
        word=shortest_negative_relation(g,support,bits)
        if expected is None:
            assert word is None
        else:
            assert word is not None and len(word)==expected
            assert g.sum(word)==0 and sum(bits[x] for x in word)%2==1
            assert len(word)<=g.n
            if g.is_boolean:
                assert len(word)<=len(g.moduli)+1
        out.append(dict(group=mods,support=support,sign_bits=bits,witness=word,
                        threshold=None if word is None else len(word)))
    return out


def check_codes():
    results = []
    cases = [((3,), [1,2], 3), ((5,),[1,4],5),
             ((2,2),[1,2,3],3), ((2,2,2),[1,2,4,7],4)]
    for mods,support,limit in cases:
        g = Group(mods)
        for D in range(2,limit+1):
            reps,masks = relation_masks(g,support,D)
            rank = binary_rank(masks)
            safe = [b for b in range(1 << len(reps))
                    if all((b & v).bit_count() % 2 == 0 for v in masks)]
            assert len(safe) == 2**(len(reps)-rank)
            # Independent integer-relation enumeration, including inverse orbits.
            integer_masks = set()
            for ns in product(range(-D,D+1), repeat=len(reps)):
                if sum(abs(a) for a in ns) > D: continue
                xs = []
                for xi,a in zip(reps,ns):
                    xs.extend([xi if a >= 0 else g.neg[xi]]*abs(a))
                if g.sum(xs) == 0:
                    integer_masks.add(sum((a % 2) << j for j,a in enumerate(ns)))
            assert masks | {0} == integer_masks
            results.append(dict(group=mods,support=support,D=D,rank=rank,safe_sign_vectors=len(safe)))
    # Unremovable negative sign on Z/5: no circle character takes value -1.
    # Algebraic certificate: chi(a)^5=1 precludes chi(a)=-1.
    return results


def theta(r):
    # Endpoints 0,1; paths 0--a_i--b_i--1.
    return graph(2+2*r, [(u,v) for i in range(r)
                         for u,v in [(0,2+2*i),(2+2*i,3+2*i),(3+2*i,1)]])


def check_theta():
    out=[]
    for q in [3,5,7]:
        g=Group((q,)); p=F(1,2); a=F(-1,8)
        coeff=[F(0)]*q; coeff[0]=p; coeff[1]=coeff[-1]=a
        # Parallel three-step paths: total = sum of products of cubed coefficients.
        direct=F(0)
        for xs in product([0,1,q-1],repeat=q):
            if sum(xs)%q == 0:
                direct += prod(coeff[x]**3 for x in xs)
        formula=sum((comb(q,2*j)*comb(2*j,j)*p**(3*(q-2*j))*a**(6*j)
                     for j in range((q-1)//2+1)),F(0))+2*a**(3*q)
        assert direct == formula
        assert direct >= p**(3*q)
        assert a**(3*q) < 0
        h=theta(q)
        # Explicit all-1, all-minus-1 relation on q odd paths.
        edge_labels=[]
        for _ in range(q): edge_labels.extend([1,q-1,1])
        assert all(g.sum(edge_labels[k] for _,k in h['adj'][v]) == 0 for v in range(h['n']))
        assert prod(coeff[x] for x in edge_labels) < 0
        out.append(dict(q=q,density=str(direct),negative_term=str(a**(3*q))))
    return out


def check_small_graphs():
    rng=random.Random(20261007)
    graphs = {
        'C4': graph(4,[(0,1),(1,2),(2,3),(3,0)]),
        'C6': graph(6,[(i,(i+1)%6) for i in range(6)]),
        'K23': graph(5,[(u,v) for u in range(2) for v in range(2,5)]),
        'K33': graph(6,[(u,v) for u in range(3) for v in range(3,6)]),
        'theta_3_3': theta(3),
        'two_C4_at_vertex': graph(7,[(0,1),(1,2),(2,3),(3,0),(0,4),(4,5),(5,6),(6,0)]),
        'tree': graph(5,[(0,1),(1,2),(1,3),(3,4)])}
    records=[]
    for mods in [(2,),(2,2)]:
        g=Group(mods)
        values_sets = [[F(0)]+[F(1)]*(g.n-1)]
        values_sets += [[F(rng.randrange(1,8),8) for _ in range(g.n)] for __ in range(3)]
        for name,h in graphs.items():
            cycles=cycle_counts(h)
            for case,values in enumerate(values_sets):
                coeff=fourier_boolean(g,values); p=coeff[0]; m=len(h['edges'])
                assert p>0
                weights=[prod((coeff[x] for x in xs),start=F(1)) for xs in flow_values(h,g)]
                t=sum(weights,F(0))
                assert t == primal_density(h,g,values)
                neg=-sum((z for z in weights if z<0),F(0))
                ds={len(ns) for ns in h['adj']}
                moment={d:moments(g,coeff,d) for d in ds}
                for d,(M,S,D) in moment.items():
                    assert S == sum((x**d for x in values),F(0))/g.n
                    assert D>=0 and M>=S>=0
                errors=[]
                for side in [0,1]:
                    side_degrees=[len(h['adj'][v]) for v in range(h['n']) if h['colors'][v]==side]
                    A=prod((moment[d][0] for d in side_degrees),start=F(1))
                    B=prod((moment[d][1] for d in side_degrees),start=F(1))
                    errors.append((A-B)/2)
                err=min(errors)
                cyc=sum((c*p**(m-ell)*sum((abs(x)**ell for x in coeff[1:]),F(0))
                         for ell,c in cycles.items()),F(0))
                assert neg<=err
                assert t>=p**m+cyc-err
                if name=='tree': assert t==p**m
                # Verify the beta/4 cut-norm bound exactly by enumerating subsets.
                beta=max(map(abs,coeff[1:]),default=F(0))
                cut=F(0)
                for A in range(1<<g.n):
                    for B in range(1<<g.n):
                        v=sum((values[g.add[x][g.neg[y]]]-p for x in range(g.n) if A>>x&1
                               for y in range(g.n) if B>>y&1),F(0))/g.n**2
                        cut=max(cut,abs(v))
                assert 4*cut<=beta
                if cycles:
                    girth=min(cycles)
                    assert cycles[girth]*p**(m-girth)*beta**girth <= t-p**m+err
                records.append(dict(group=mods,graph=name,case=case,flows=len(weights),
                                    density=str(t),negative_flow_mass=str(neg),
                                    local_error=str(err),cut_norm=str(cut)))
    return records


def check_incidence():
    pair_count=Counter(pair for face in FACES for pair in combinations(face,2))
    assert len(FACES)==22 and len(set(FACES))==22
    assert len(pair_count)==33 and set(pair_count.values())=={2}
    deg=Counter(i for face in FACES for i in face)
    assert sorted(deg)==list(range(13)) and sum(deg.values())==66
    c4=sum(comb(n,2) for n in pair_count.values())
    assert c4==33
    triangles={t for t in combinations(range(13),3)
               if all(pair in pair_count for pair in combinations(t,2))}
    assert triangles==set(FACES)
    c6=4*len(triangles)
    assert c6==88
    h=graph(35,[(i,13+j) for j,face in enumerate(FACES) for i in face])
    assert len(h['roots'])==1 and len(h['chords'])==32
    # Exact one-character density: conditional averaging over each face vertex.
    mono=Counter()
    for mask in range(1<<13):
        k=sum(len({(mask>>i)&1 for i in face})==1 for face in FACES)
        mono[k]+=1
    assert sum(mono.values())==8192
    poly=[0]*23
    for k,count in mono.items():
        for a in range(k+1):
            for b in range(22-k+1):
                poly[a+b]+=count*comb(k,a)*3**a*comb(22-k,b)*(-1)**b
    assert all(x%8192==0 for x in poly)
    poly=[x//8192 for x in poly]
    assert poly[0]==1 and poly[1]==0 and poly[2]==33 and poly[3]==c6
    assert all(x>=0 for x in poly)
    assert sum(poly)==2**32
    p=F(1,2); t=F(1,10); z=(t/p)**2
    density=p**66*sum((a*z**j for j,a in enumerate(poly)),F(0))
    conditional=sum((count*(p**3+3*p*t*t)**k*(p**3-p*t*t)**(22-k)
                     for k,count in mono.items()),F(0))/8192
    assert density==conditional
    assert density>=p**66+33*p**62*t**4
    return dict(vertices=35,edges=66,point_degrees=[deg[i] for i in range(13)],
                distinct_point_pairs=33,pair_multiplicity=2,connected=True,girth=4,
                four_cycles=33,six_cycles=c6,point_graph_triangles=len(triangles),cycle_space_dimension=32,
                mono_face_distribution=dict(sorted(mono.items())),
                eulerian_polynomial_variable='z=(t/p)^2',eulerian_polynomial_coefficients=poly,
                polynomial_coefficient_sum=sum(poly),sample_density=str(density))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=parser.parse_args()
    face_file=Path(__file__).with_name('faces.json')
    if face_file.exists():
        data=json.loads(face_file.read_text(encoding='utf-8'))
        assert data['points']==13 and data['faces']==[list(f) for f in FACES]
    result={'status':'passed','arithmetic':'exact integers and fractions; no floating-point assertions',
            'seed':20261007,'scope':'finite regression checks, not a formal proof or exhaustive search',
            'sign_codes':check_codes(),'shortest_relations':check_shortest_relations(),
            'theta_obstructions':check_theta(),
            'small_graphs':check_small_graphs(),'incidence_pattern':check_incidence()}
    result['summary']={'sign_code_cases':len(result['sign_codes']),
                       'theta_cases':len(result['theta_obstructions']),
                       'shortest_relation_cases':len(result['shortest_relations']),
                       'graph_host_cases':len(result['small_graphs'])}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result['summary'],indent=2))
    print('All exact checks passed.')
    print('Incidence Eulerian polynomial:',result['incidence_pattern']['eulerian_polynomial_coefficients'])

if __name__=='__main__':
    main()
