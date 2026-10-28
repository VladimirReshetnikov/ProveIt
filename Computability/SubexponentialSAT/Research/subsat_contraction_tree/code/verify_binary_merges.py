#!/usr/bin/env python3
"""Independent finite algebra checks; no asymptotic runtime benchmark.

Tests tables built by binary matrix contractions against direct tensor sums,
and verifies exact CRT coordinate lifts over Z/(2^p) and
(Z/(2^p))[U,V]/(U^2+U+1,V^2). Standard library only.
"""
import itertools
import json
import random
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class Ring:
    def __init__(self, p, extension=False):
        self.mod = 1 << p
        self.dim = 4 if extension else 1
        self.zero = (0,) * self.dim
        self.one = (1,) + (0,) * (self.dim - 1)

    def add(self, x, y):
        return tuple((a+b) % self.mod for a, b in zip(x, y))

    def basis_product(self, i, j):
        if self.dim == 1:
            return ((0, 1),)
        v = i//2 + j//2
        u = i%2 + j%2
        if v >= 2:
            return ()
        if u == 2:
            return ((2*v, -1), (2*v+1, -1))
        return ((2*v+u, 1),)

    def mul(self, x, y):
        z = [0]*self.dim
        for i, xi in enumerate(x):
            for j, yj in enumerate(y):
                for k, sign in self.basis_product(i, j):
                    z[k] += sign*xi*yj
        return tuple(c % self.mod for c in z)

    def random(self, rng):
        return tuple(rng.randrange(self.mod) for _ in range(self.dim))


def assignments(axes, dims):
    return itertools.product(*(range(dims[e]) for e in axes))


def factors(r, dims, ring, rng):
    answer = {}
    for g in range(r):
        axes = tuple(e for e in sorted(dims) if g in e)
        answer[g] = (axes, {a: ring.random(rng) for a in assignments(axes,dims)})
    return answer


def entry(table, env):
    axes, data = table
    return data[tuple(env[e] for e in axes)]


def naive_table(vertices, fs, dims, ring):
    vertices = frozenset(vertices)
    boundary = tuple(e for e in sorted(dims) if (e[0] in vertices) != (e[1] in vertices))
    inside = tuple(e for e in sorted(dims) if e[0] in vertices and e[1] in vertices)
    data = {}
    for ext in assignments(boundary,dims):
        env = dict(zip(boundary,ext)); acc=ring.zero
        for inn in assignments(inside,dims):
            env.update(zip(inside,inn)); term=ring.one
            for g in sorted(vertices):
                term=ring.mul(term,entry(fs[g],env))
            acc=ring.add(acc,term)
        data[ext]=acc
    return boundary,data


def merge_tables(ta,tb,dims,ring):
    # Independent matricization: left external, shared inner, right external.
    aa,bb=set(ta[0]),set(tb[0])
    common=tuple(sorted(aa&bb)); left=tuple(sorted(aa-bb)); right=tuple(sorted(bb-aa))
    output_axes=tuple(sorted(aa^bb))
    data={}
    for x in assignments(left,dims):
        for y in assignments(right,dims):
            env=dict(zip(left,x)); env.update(zip(right,y)); acc=ring.zero
            for z in assignments(common,dims):
                env.update(zip(common,z))
                acc=ring.add(acc,ring.mul(entry(ta,env),entry(tb,env)))
            data[tuple(env[e] for e in output_axes)]=acc
    return output_axes,data


def tree_table(vs,fs,dims,ring,ledger):
    if len(vs)==1:
        return fs[vs[0]]
    pivot=len(vs)//2
    a,b=vs[:pivot],vs[pivot:]
    ta=tree_table(a,fs,dims,ring,ledger)
    tb=tree_table(b,fs,dims,ring,ledger)
    actual=merge_tables(ta,tb,dims,ring)
    expected=naive_table(vs,fs,dims,ring)
    require(actual==expected,'binary merge does not equal independent direct sum')
    ledger['merge_tables']+=1
    ledger['table_entries']+=len(actual[1])
    return actual


def triangle(tables,dims,ring):
    axes=tuple(sorted(set().union(*(set(t[0]) for t in tables))))
    require(all(sum(e in t[0] for t in tables)==2 for e in axes),'triangle edge incidence')
    total=ring.zero
    for a in assignments(axes,dims):
        env=dict(zip(axes,a)); term=ring.one
        for t in tables:
            term=ring.mul(term,entry(t,env))
        total=ring.add(total,term)
    return total


def schoolbook(a,b,ring):
    m,k,n=len(a),len(b),len(b[0]); out=[[ring.zero for _ in range(n)] for _ in range(m)]
    for i in range(m):
        require(len(a[i])==k,'incompatible matrix dimension')
        for j in range(n):
            for h in range(k):
                out[i][j]=ring.add(out[i][j],ring.mul(a[i][h],b[h][j]))
    return out


def crt(values,primes):
    x=0; modulus=1
    for value,prime in zip(values,primes):
        step=((value-x)*pow(modulus,-1,prime))%prime
        x+=modulus*step; modulus*=prime
    return x


def crt_matrix(a,b,ring):
    m,k,n=len(a),len(b),len(b[0]); bound=k*(ring.mod-1)**2
    primes=[]; product=1
    for q in [101,103,107,109,113,127,131,137,139,149]:
        primes.append(q); product*=q
        if product>bound: break
    require(product>bound,'insufficient CRT modulus')
    out=[[[0]*ring.dim for _ in range(n)] for _ in range(m)]
    # Each coordinate pair is an integer matrix product. No target-ring inverse.
    for x in range(ring.dim):
        for y in range(ring.dim):
            structure=ring.basis_product(x,y)
            if not structure: continue
            for i in range(m):
                for j in range(n):
                    residues=[sum(a[i][h][x]*b[h][j][y] for h in range(k))%q for q in primes]
                    value=crt(residues,primes)
                    require(0<=value<=bound,'CRT integer reconstruction bound')
                    for z,sign in structure:
                        out[i][j][z]+=sign*value
    return [[tuple(v%ring.mod for v in cell) for cell in row] for row in out]


def main():
    ledger={'networks':0,'merge_tables':0,'table_entries':0,'triangles':0,
            'rectangular_crt_products':0,'crt_entries':0,'negative_controls':0}
    rng=random.Random(20261026)
    for extension in [False,True]:
        for p in [1,3,7]:
            ring=Ring(p,extension)
            for r in [3,4]:
                for fixture in range(4):
                    dims={(g,h):2 if fixture!=1 or (g+h)%3 else 1 for g in range(r) for h in range(r) if g!=h}
                    if fixture==2:
                        dims[(0,1)]=0
                    fs=factors(r,dims,ring,rng)
                    computed=tree_table(list(range(r)),fs,dims,ring,ledger)
                    direct=naive_table(range(r),fs,dims,ring)
                    require(computed==direct,'complete contraction mismatch')
                    blocks=[[0],[1],list(range(2,r))]
                    tables=[tree_table(b,fs,dims,ring,ledger) for b in blocks]
                    require(triangle(tables,dims,ring)==direct[1][()], 'three-block contraction mismatch')
                    ledger['networks']+=1;ledger['triangles']+=1
            for m,k,n in [(1,1,1),(2,3,4),(4,2,3),(3,5,2)]:
                for _ in range(3):
                    a=[[ring.random(rng) for _ in range(k)] for _ in range(m)]
                    b=[[ring.random(rng) for _ in range(n)] for _ in range(k)]
                    require(crt_matrix(a,b,ring)==schoolbook(a,b,ring),'CRT coordinate product mismatch')
                    ledger['rectangular_crt_products']+=1;ledger['crt_entries']+=m*n
    # Algebraic edge cases and nontrivial negative controls.
    ring=Ring(3,True); U=(0,1,0,0); V=(0,0,1,0)
    require(ring.add(ring.add(ring.mul(U,U),U),ring.one)==ring.zero,'unramified relation')
    require(ring.mul(V,V)==ring.zero,'nilpotent relation')
    try: require(ring.mul(U,U)==ring.one,'intentionally false ring identity')
    except RuntimeError: ledger['negative_controls']+=1
    else: raise RuntimeError('negative control escaped')
    try: schoolbook([[ring.one]],[[ring.one],[ring.one]],ring)
    except RuntimeError: ledger['negative_controls']+=1
    else: raise RuntimeError('bad dimensions accepted')
    result={'status':'pass','claims_checked':'finite algebra, not asymptotic theorem or SAT benchmark',
            'rings':['Z/(2^p)','(Z/(2^p))[U,V]/(U^2+U+1,V^2)'],
            'precision_bits':[1,3,7],'seed':20261026,'checks':ledger}
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if len(sys.argv)>1: Path(sys.argv[1]).write_text(encoded)
    print(encoded,end='')


if __name__=='__main__': main()
