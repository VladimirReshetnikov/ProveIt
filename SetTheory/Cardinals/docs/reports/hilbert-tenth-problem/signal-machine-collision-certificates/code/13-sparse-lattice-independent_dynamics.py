"""Independent dense and unit-record dynamics for fixed conservative local permutations.
No dependencies on the certificate producer's implementation.
"""
from collections import Counter, defaultdict
from itertools import product, permutations
import random


def conservative_permutation(K, rng):
    fibers = defaultdict(list)
    for state in product(range(K + 1), repeat=3):
        fibers[sum(state)].append(state)
    table = {}
    for fiber in fibers.values():
        images = list(fiber)
        rng.shuffle(images)
        table.update(zip(fiber, images))
    return table


def dense_step(conf, table):
    # A channel 0,1,2 has velocity -1,0,+1. Collision follows streaming.
    streamed = defaultdict(lambda: [0, 0, 0])
    for x, lanes in conf.items():
        for c, n in enumerate(lanes):
            streamed[x+c-1][c] += n
    return {x: table[tuple(lanes)] for x, lanes in streamed.items()
            if sum(lanes)}


def to_records(conf):
    return sorted((x, c) for x, lanes in conf.items()
                  for c, n in enumerate(lanes) for _ in range(n))


def from_records(records):
    out = defaultdict(lambda: [0, 0, 0])
    for x,c in records:
        out[x][c] += 1
    return {x: tuple(a) for x,a in out.items()}


def sparse_step(records, table):
    # Streaming preserves records. Collision is determined for every record by
    # full pairwise counting, and same-position ranks distribute outgoing mass.
    streamed = [(x+c-1,c) for x,c in records]
    result = []
    for i, (x,c) in enumerate(streamed):
        incoming = tuple(sum(y==x and d==j for y,d in streamed) for j in range(3))
        outgoing = table[incoming]
        rank = sum(y==x for y,_ in streamed[:i+1])
        new_c = 0 if rank<=outgoing[0] else (1 if rank<=outgoing[0]+outgoing[1] else 2)
        result.append((x,new_c))
    # Deliberately no hidden identifiers.
    return sorted(result)


def exhaustive():
    checked = 0
    for K in (1,2):
        for seed in range(10):
            rng = random.Random((K,seed).__repr__())
            table = conservative_permutation(K,rng)
            configs = (product(range(K+1),repeat=6) if K==1 else
                       (tuple(rng.randrange(K+1) for _ in range(6)) for _ in range(200)))
            for values in configs:
                dense = {0:tuple(values[:3]),3:tuple(values[3:])}
                dense = {x:a for x,a in dense.items() if sum(a)}
                sparse=to_records(dense)
                M=len(sparse)
                for t in range(5):
                    dense = dense_step(dense,table)
                    sparse = sparse_step(sparse,table)
                    assert sparse==to_records(dense)
                    assert len(sparse)==M
                    assert all(-t-1<=x<=3+t+1 for x,c in sparse)
                    assert all(0<=n<=K for lanes in dense.values() for n in lanes)
                    checked += 1
    return checked

def exhaustive_binary_rules():
    fibers = defaultdict(list)
    for a in product(range(2), repeat=3):
        fibers[sum(a)].append(a)
    checked=0
    for p1,p2 in product(permutations(fibers[1]),permutations(fibers[2])):
        table={(0,0,0):(0,0,0),(1,1,1):(1,1,1)}
        table.update(zip(fibers[1],p1))
        table.update(zip(fibers[2],p2))
        for vals in product(range(2),repeat=9):
            dense={x:tuple(vals[3*x:3*x+3]) for x in range(3)}
            dense={x:a for x,a in dense.items() if sum(a)}
            records=to_records(dense)
            for t in range(4):
                dense=dense_step(dense,table)
                records=sparse_step(records,table)
                assert records==to_records(dense)
                checked+=1
    return checked

if __name__=='__main__':
    import json
    print(json.dumps({'randomized_dense_sparse_steps_checked': exhaustive(),
                      'all_36_binary_rules_steps_checked': exhaustive_binary_rules(),
                      'passes': ['mass', 'canonical_records', 'all_collisions', 'capacity', 'light_cone']}, indent=2))
