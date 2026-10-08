"""Independent, literal-sheet oracle for the binary boundary transport kernel.

The oracle uses breadth-first propagation of equivariance over explicitly
materialized generator permutations.  It does not use gcd/orbit formulas,
the production component classifier, CRT, or the rooted transport formula.
Run with PYTHONPATH pointing at Topology/UnknotRecognition/fast.
"""

from collections import deque
from itertools import product
from math import gcd
import argparse
import json
import time

from bootstrap import enable_fast
enable_fast()
from fastunknot.boundary_transport import BoundaryTransportIndex


def example(n, maps, orientable=True, genus=0):
    rank = len(maps)
    boundaries = rank-(2*genus if orientable else genus)+1
    return {'surface': {'orientable': orientable, 'genus': genus,
                        'boundary_components': boundaries},
            'sheets': n,
            'monodromy': [{'sign': sign, 'shift': shift} for sign, shift in maps]}


def literal_model(raw):
    n = raw['sheets']
    maps = [tuple((a['sign']*x+a['shift']) % n for x in range(n))
            for a in raw['monodromy']]
    inverses = []
    for permutation in maps:
        inverse = [None]*n
        for x, y in enumerate(permutation):
            inverse[y] = x
        inverses.append(tuple(inverse))

    surface = raw['surface']
    genus = surface['genus']
    prefix = []
    if surface['orientable']:
        for j in range(genus):
            a, b = 2*j+1, 2*j+2
            prefix.extend((a,b,-a,-b))
        next_generator = 2*genus+1
    else:
        for j in range(genus):
            prefix.extend((j+1,j+1))
        next_generator = genus+1
    words = []
    for j in range(surface['boundary_components']-1):
        generator = next_generator+j
        words.append([generator])
        prefix.append(generator)
    words.append([-letter for letter in reversed(prefix)])
    peripheral = []
    for word in words:
        permutation = []
        for x in range(n):
            for letter in word:
                x = (maps if letter > 0 else inverses)[abs(letter)-1][x]
            permutation.append(x)
        peripheral.append(tuple(permutation))

    unseen = set(range(n))
    components = []
    while unseen:
        component = {min(unseen)}
        pending = deque(component)
        while pending:
            x = pending.popleft()
            for permutation in maps:
                y = permutation[x]
                if y not in component:
                    component.add(y)
                    pending.append(y)
        unseen.difference_update(component)
        components.append(tuple(sorted(component)))
    return maps, peripheral, components


def literal_maps(generators, source, target):
    if len(source) != len(target):
        return []
    root = min(source)
    result = []
    for image in target:
        mapping = {root: image}
        pending = deque([root])
        consistent = True
        while pending and consistent:
            x = pending.popleft()
            for permutation in generators:
                y, expected = permutation[x], permutation[mapping[x]]
                if y in mapping:
                    if mapping[y] != expected:
                        consistent = False
                        break
                else:
                    mapping[y] = expected
                    pending.append(y)
        if consistent and len(mapping) == len(source) and set(mapping.values()) == set(target):
            result.append(mapping)
    return result


def literal_orbit(permutation, sheet):
    orbit = {sheet}
    current = permutation[sheet]
    while current != sheet:
        orbit.add(current)
        current = permutation[current]
    return frozenset(orbit)


def audit(max_rank_two=5, max_rank_one=8):
    counts = {'presentations': 0, 'component_pairs': 0, 'unmarked_queries': 0,
              'point_queries': 0, 'boundary_queries': 0,
              'double_boundary_queries': 0, 'mixed_queries': 0,
              'literal_transport_values': 0}
    start = time.perf_counter()
    presentations = []
    for n in range(1,max_rank_one+1):
        for sign, shift in product((-1,1),range(n)):
            for orientable, genus in ((True,0),(False,1)):
                presentations.append(example(n, [(sign,shift)], orientable, genus))
    for n in range(1,max_rank_two+1):
        generators = list(product((-1,1),range(n)))
        for maps in product(generators, repeat=2):
            for orientable, genus in ((True,0),(True,1),(False,1)):
                presentations.append(example(n, maps, orientable, genus))
    # Empty-generator disk and larger fixed/paired components are included.
    for n in range(1,9):
        presentations.append(example(n, []))
    for n,d in ((12,4),(16,4),(18,6),(24,8),(30,10)):
        presentations.append(example(n, [(1,d),(-1,0)]))

    for raw in presentations:
        counts['presentations'] += 1
        index = BoundaryTransportIndex(raw)
        generators, peripheral, components = literal_model(raw)
        orbits = [[literal_orbit(p,x) for x in range(raw['sheets'])]
                  for p in peripheral]
        for source in components:
            for target in components:
                counts['component_pairs'] += 1
                maps = literal_maps(generators, source, target)
                root = min(source)

                def compare(points=(), boundaries=(), category='unmarked_queries'):
                    counts[category] += 1
                    expected = [f for f in maps
                                if all(f[x] == y for x,y in points)
                                and all(f[x] in orbits[b][y] for b,x,y in boundaries)]
                    result = index.transports(source[-1], target[-1],
                                              point_pairs=points, boundary_pairs=boundaries)
                    images = set()
                    for progression in result['root_progressions']:
                        expanded = {progression['first']+j*progression['step']
                                    for j in range(progression['count'])}
                        assert not images & expanded, (raw,result)
                        images.update(expanded)
                    assert result['source_root'] == root, (raw,result,source)
                    assert images == {f[root] for f in expected}, (raw,points,boundaries,result,expected)
                    assert result['isomorphism_count'] == len(expected), (raw,result,expected)
                    assert len(result['root_progressions']) <= 2
                    assert result['witness_target_anchor'] == (min(images) if images else None)
                    if points:
                        assert len(expected) <= 1
                    if expected and boundaries:
                        boundary_gcd = 0
                        for b,x,y in boundaries:
                            boundary_gcd = gcd(boundary_gcd,len(orbits[b][x]))
                        assert boundary_gcd % len(expected) == 0
                    return expected

                expected = compare()
                for f in expected:
                    for x in source:
                        counts['literal_transport_values'] += 1
                        assert index.transport_sheet(root,f[root],x) == f[x]
                for x,y in product(source,target):
                    compare([(x,y)], category='point_queries')
                    for b in range(len(peripheral)):
                        compare(boundaries=[(b,x,y)], category='boundary_queries')
                # Exhaust every ordered pair on the full rank-one/rank-two
                # small-fibre grid; larger fixtures use a deterministic subset.
                pairs = list(product(source,target))
                if raw['sheets'] > max(max_rank_one,max_rank_two):
                    pairs = pairs[:4]
                for (x,y),(u,v) in product(pairs,repeat=2):
                    compare(boundaries=[(0,x,y),(len(peripheral)-1,u,v)],
                            category='double_boundary_queries')
                    compare(points=[(x,y)], boundaries=[(len(peripheral)-1,u,v)],
                            category='mixed_queries')
    counts['total_queries'] = sum(counts[name] for name in (
        'unmarked_queries','point_queries','boundary_queries',
        'double_boundary_queries','mixed_queries'))
    counts['elapsed_seconds'] = time.perf_counter()-start
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank-two-max',type=int,default=5)
    parser.add_argument('--rank-one-max',type=int,default=8)
    parser.add_argument('--output')
    args = parser.parse_args()
    result = audit(args.rank_two_max,args.rank_one_max)
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    print(text,end='')
