#!/usr/bin/env python3
"""Construct and independently verify prime-disjoint directed modular routes.

Standard library only. The experiments are illustrations, not a proof of GRH
or verification of the asymptotic sufficient inequalities in the paper.
"""
import argparse
import json
import math
import random
from pathlib import Path


def primes_up_to(y):
    a = bytearray(b'\x01') * (y + 1)
    a[0:2] = b'\x00\x00'
    for p in range(2, math.isqrt(y) + 1):
        if a[p]:
            a[p*p:y+1:p] = b'\x00' * ((y-p*p)//p+1)
    return [p for p in range(2,y+1) if a[p]]


class Graph:
    def __init__(self, q, primes, allowed):
        self.q = q
        self.vertices = tuple(x for x in range(1,q) if math.gcd(x,q)==1)
        self.primes = tuple(primes)
        assert len(set(primes)) == len(primes)
        assert all(p < q and math.gcd(p,q)==1 for p in primes)
        self.allowed = {x: set(allowed[x]) for x in self.vertices}
        assert all(s <= set(primes) for s in self.allowed.values())
        self.inverse = {p: pow(p,-1,q) for p in primes}
        self.incoming = {x:set() for x in self.vertices}
        for x, ps in self.allowed.items():
            for p in ps:
                self.incoming[(x*p)%q].add(p)

    def degree_minima(self, pool=None):
        pool = set(self.primes if pool is None else pool)
        return (min(len(ps & pool) for ps in self.allowed.values()),
                min(len(ps & pool) for ps in self.incoming.values()))


def make_graph(q,y,seed,keep=0.86):
    rng = random.Random(seed)
    primes = [p for p in primes_up_to(y) if q%p]
    vertices = [x for x in range(1,q) if math.gcd(x,q)==1]
    # Independent edge deletions, not just global prime deletions.
    allowed = {x:[p for p in primes if rng.random()<keep] for x in vertices}
    return Graph(q,primes,allowed)


def witness_ball(g, start, pool, forbidden_labels, forbidden_vertices, k, reverse=False):
    """One stored rainbow witness per endpoint; witnesses stay valid as the ball grows."""
    labels = sorted(set(pool)-set(forbidden_labels))
    allowed_vertices = set(g.vertices)-set(forbidden_vertices)
    assert start in allowed_vertices
    witnesses = {start: ()}
    for _ in range(k):
        if len(witnesses)*2 > len(g.vertices):
            break
        new = {}
        for x, path in witnesses.items():
            seen_labels = set(path)
            if reverse:
                for p in labels:
                    if p in seen_labels or p not in g.incoming[x]:
                        continue
                    z = x*g.inverse[p] % g.q
                    if z in allowed_vertices and z not in witnesses and z not in new:
                        new[z] = (p,) + path
            else:
                for p in labels:
                    if p in seen_labels or p not in g.allowed[x]:
                        continue
                    z = x*p % g.q
                    if z in allowed_vertices and z not in witnesses and z not in new:
                        new[z] = path + (p,)
        if not new:
            break
        witnesses.update(new)
    return witnesses


def erase_cycles(q, source, labels):
    vertices = [source]
    result = []
    for p in labels:
        nxt = vertices[-1]*p % q
        if nxt in vertices:
            i = vertices.index(nxt)
            vertices = vertices[:i+1]
            result = result[:i]
        else:
            vertices.append(nxt)
            result.append(p)
    return vertices, result


def route(g,s,t,pools,F,W,k):
    left = witness_ball(g,s,pools[0],F,W,k)
    right = witness_ball(g,t,pools[1],F,W,k,reverse=True)
    common = left.keys() & right.keys()
    if not common:
        return None
    m = min(common, key=lambda x:(len(left[x])+len(right[x]),x))
    vertices, labels = erase_cycles(g.q,s,left[m]+right[m])
    assert vertices[-1]==t
    return {'source':s,'target':t,'vertices':vertices,'primes':labels,
            'forward_ball':len(left),'reverse_ball':len(right)}


def route_pairs(g,pairs,pools,k):
    terminals = {v for pair in pairs for v in pair}
    assert len(terminals)==2*len(pairs)
    used_p=set(); used_v=set(); routes=[]
    for s,t in pairs:
        W = (terminals-{s,t}) | used_v
        r = route(g,s,t,pools,used_p,W,k)
        if r is None:
            return None
        used_p.update(r['primes'])
        used_v.update(r['vertices'][1:-1])
        routes.append(r)
    return routes


def verify(g,pairs,routes,k):
    """Verify only the exact certificates; no spectral or asymptotic assumptions."""
    assert len(pairs)==len(routes)
    all_labels=set(); all_vertices=set()
    for (s,t),r in zip(pairs,routes):
        vs,ps=r['vertices'],r['primes']
        assert r['source']==s and r['target']==t
        assert vs[0]==s and vs[-1]==t and len(vs)==len(ps)+1
        assert len(ps)<=2*k and len(set(ps))==len(ps) and len(set(vs))==len(vs)
        assert not (all_labels & set(ps)) and not (all_vertices & set(vs))
        for x,p,z in zip(vs,ps,vs[1:]):
            assert p in g.primes and p in g.allowed[x] and z==x*p%g.q
        all_labels.update(ps); all_vertices.update(vs)
    return {'verified':True,'number_of_routes':len(routes),
            'total_primes':len(all_labels),'max_length':max(map(lambda r:len(r['primes']),routes),default=0)}


def example(q,y,seed,count=10,k=4):
    g=make_graph(q,y,seed)
    rng=random.Random(seed+1000)
    ts=rng.sample(g.vertices,2*count)
    pairs=list(zip(ts[::2],ts[1::2]))
    for attempt in range(1,101):
        labels=list(g.primes); rng.shuffle(labels)
        h=len(labels)//2; pools=[labels[:h],labels[h:]]
        if any(2*min(g.degree_minima(P))<=len(P) for P in pools):
            continue
        routes=route_pairs(g,pairs,pools,k)
        if routes is None:
            continue
        result=verify(g,pairs,routes,k)
        return {'q':q,'y':y,'seed':seed,'keep_probability':0.86,'k':k,
                'n':len(g.vertices),'d':len(g.primes),'min_degrees':g.degree_minima(),
                'pools':pools,'pool_min_degrees':[g.degree_minima(P) for P in pools],
                'attempt':attempt,'pairs':pairs,'routes':routes,**result}
    raise RuntimeError('No witness in 100 attempts (not evidence against theorem).')


def verify_file(path):
    data=json.loads(Path(path).read_text())
    for row in data['examples']:
        g=make_graph(row['q'],row['y'],row['seed'],row['keep_probability'])
        assert len(g.vertices)==row['n'] and len(g.primes)==row['d']
        assert list(g.degree_minima())==row['min_degrees']
        a,b=map(set,row['pools']); assert not a&b and a|b==set(g.primes)
        assert [list(g.degree_minima(P)) for P in row['pools']]==row['pool_min_degrees']
        res=verify(g,row['pairs'],row['routes'],row['k'])
        assert all(row[key]==val for key,val in res.items())
        print(f"q={row['q']}: {res}")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='examples.json')
    parser.add_argument('--verify',metavar='JSON')
    args=parser.parse_args()
    if args.verify:
        verify_file(args.verify)
        return
    data={'description':'Exact finite route certificates in randomly locally damaged graphs. Not a spectral proof.',
          'examples':[example(1009,600,41),example(1155,600,42),example(5003,900,43)]}
    Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
    verify_file(args.output)


if __name__=='__main__':
    main()
