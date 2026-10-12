"""Reproducible geometric fixtures and exact cochain-isomorphism keys."""
from itertools import permutations

from normal_orbit_research.fixtures import layered_torus
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.pachner23 import pachner_23
from fastunknot.cocycle_transport import transport_cocycle


def independent_bipyramids(count):
    """A solid torus with count independent inverse 3--2 regions.

    Perform one 2--3 move inside each disjoint adjacent pair of tetrahedra
    in the 2*count Fibonacci layered torus.  Each final three-cell block is
    an inverse region.  The returned construction trace authenticates the
    solid-torus provenance independently of the search implementation.
    """
    if type(count) is not int or count < 1:
        raise ValueError('count must be positive')
    source, _ = layered_torus(2*count)
    initial = rank_one_cocycle_seed(source)['heights']
    raw, heights, surviving = source, initial, list(range(2*count))
    trace, regions = [], []
    for i in range(count):
        t = surviving.index(2*i)
        other = surviving.index(2*i+1)
        face = next(f for f, entry in enumerate(raw['tetrahedra'][t])
                    if entry is not None and entry['tetrahedron'] == other)
        replacement = pachner_23(raw, t, face)
        transported = transport_cocycle(raw, heights, replacement['triangulation'],
                                       replacement['certificate'])
        trace.append(dict(triangulation=replacement['triangulation'],
                          transport=transported['certificate']))
        survivors = [old for j, old in enumerate(surviving) if j not in (t, other)]
        survivors.extend([('region', i, j) for j in range(3)])
        surviving = survivors
        raw, heights = replacement['triangulation'], transported['heights']
    for i in range(count):
        regions.append([surviving.index(('region', i, j)) for j in range(3)])
    return dict(source=source, source_heights=initial, triangulation=raw,
                heights=heights, regions=regions, construction=trace)


def canonical_cochain_key(raw, heights):
    """Exact rooted-traversal minimum over 24*t coordinate relabellings.

    Used only by finite differential audits, not by the search or verifier.
    It identifies precisely face-pairing isomorphisms carrying the signed
    integral cochain.  Cohomologous but differently gauged vertex data are
    intentionally not identified.
    """
    rows = raw['tetrahedra']
    candidates = []
    for root in range(len(rows)):
        for first in permutations(range(4)):
            order, number, labels = [root], {root: 0}, {root: first}
            for t in order:
                lab = labels[t]
                inverse = [lab.index(v) for v in range(4)]
                for f in range(4):
                    entry = rows[t][inverse[f]]
                    if entry is None:
                        continue
                    u, perm = entry['tetrahedron'], entry['permutation']
                    if u not in number:
                        number[u] = len(order)
                        order.append(u)
                        other = [0]*4
                        for v in range(4):
                            other[perm[v]] = lab[v]
                        labels[u] = tuple(other)
            if len(order) != len(rows):
                raise ValueError('the canonical-key audit expects a connected dual graph')
            result = []
            for t in order:
                lab = labels[t]
                inverse = [lab.index(v) for v in range(4)]
                faces = []
                for f in range(4):
                    entry = rows[t][inverse[f]]
                    if entry is None:
                        faces.append((-1, ()))
                    else:
                        u, perm = entry['tetrahedron'], entry['permutation']
                        faces.append((number[u], tuple(labels[u][perm[inverse[v]]]
                                                       for v in range(4))))
                h = [heights[t][v] for v in inverse]
                result.append((tuple(faces), tuple(x-h[0] for x in h)))
            candidates.append(tuple(result))
    return min(candidates)


def endpoint_keys(source, heights, certificates):
    """The exact geometric endpoint set, ignoring only vertex/cell names."""
    result = set()
    for proof in certificates:
        moves = proof['moves']
        raw = moves[-1]['triangulation'] if moves else source
        h = moves[-1]['transport']['heights'] if moves else heights
        result.add(canonical_cochain_key(raw, h))
    return result
