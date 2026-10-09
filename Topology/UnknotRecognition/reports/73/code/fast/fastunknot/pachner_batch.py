"""Simultaneous, relative-boundary 3--2 replacements with cocycle transport.

The selected degree-three edge stars must have disjoint tetrahedron sets.
They may share vertices, edges, and boundary facets.  The output is ordered
by surviving input tetrahedra, followed by two tetrahedra per canonical
region.  No intermediate full triangulations are constructed or retained.
"""
from copy import deepcopy

from .normal_cocycle import _Budget, local_coordinates
from .normal_surface_geometry import _prepare, _edge, _EDGES, NormalOrbitError
from .cocycle_transport import (
    _collapse_region, _integer_heights, _region_heights, bipyramid_cocycle_score,
)
from .cocycle_transport_verify import _shield_callback


_NEW = ((0, 1, 2, 3), (0, 1, 2, 4))


def _edge_occurrences(prepared, check):
    groups = {}
    for local, root in enumerate(prepared['edge_roots']):
        check()
        groups.setdefault(root, []).append((local // 6, *_EDGES[local % 6]))
    return groups


def _region_record(region):
    return [dict(tetrahedron=t, vertices=list(region[t])) for t in sorted(region)]


@_shield_callback
def pachner_32_regions(triangulation, heights=None, *, max_work=None,
                       check=lambda: None):
    """Find each legal degree-three star once, retaining its old corner labels.

    Optional coherent heights add exact raw Euler and normal-piece scores.
    A candidate is a move site; it is never a topology verdict.
    """
    budget = _Budget(check, max_work)
    prepared = _prepare(triangulation, budget.tick)
    h = (None if heights is None else
         _integer_heights(prepared, heights, budget.tick))
    groups = _edge_occurrences(prepared, budget.tick)
    candidates = []
    for edge, occurrences in groups.items():
        budget.tick()
        region = _collapse_region(prepared['tetrahedra'], occurrences, budget.tick)
        if region is None:
            continue
        t, a, b = occurrences[0]
        record = dict(tetrahedron=t, vertices=[a, b], edge=edge,
                      region=_region_record(region))
        if h is not None:
            five = _region_heights(region, h, budget.tick)
            score = bipyramid_cocycle_score(five)
            record.update(bipyramid_heights=five,
                          euler_gain=score['euler_loss'],
                          normal_disc_saving=score['normal_disc_increase'])
        candidates.append(record)
    return dict(candidates=candidates,
                stats=dict(work=budget.work, global_edges=len(groups),
                           candidates=len(candidates), manifold_preparations=1))


@_shield_callback
def select_disjoint_collapses(candidates, *, strategy='score', max_work=None,
                              check=lambda: None):
    """Select a deterministic maximal family of disjoint supplied stars.

    For the deduplicated census from ``pachner_32_regions``, its conflict
    graph has degree at most nine, so at least one tenth of the candidates
    are retained.  This selector does not validate ambient topology.
    """
    if type(candidates) is not list or strategy not in ('score', 'first'):
        raise ValueError('expected a candidate list and score/first strategy')
    budget = _Budget(check, max_work)
    supports, incident, roots = [], {}, set()
    for i, item in enumerate(candidates):
        budget.tick()
        if type(item) is not dict or type(item.get('region')) is not list:
            raise ValueError('each candidate must include a three-tetrahedron region')
        region = item['region']
        if (len(region) != 3 or any(type(row) is not dict
                or type(row.get('tetrahedron')) is not int for row in region)):
            raise ValueError('each candidate must include a three-tetrahedron region')
        support = {row['tetrahedron'] for row in region}
        if len(support) != 3:
            raise ValueError('a candidate repeats a tetrahedron')
        root = item.get('edge')
        if type(root) is not int or root in roots:
            raise ValueError('candidate central edges must be distinct integer roots')
        roots.add(root)
        supports.append(support)
        for t in support:
            incident.setdefault(t, []).append(i)
        if any(type(item.get(field, 0)) is not int or item.get(field, 0) < 0
               for field in ('euler_gain', 'normal_disc_saving')):
            raise ValueError('candidate scores must be nonnegative integers')
    # A tetrahedron has six local edges.  Reject a malformed purported
    # degree-three-star census before constructing an unbounded conflict list.
    if any(len(indices) > 6 for indices in incident.values()):
        raise ValueError('more than six candidate central edges meet one tetrahedron')
    neighbours = [set() for _ in candidates]
    for indices in incident.values():
        budget.tick()
        for i in indices:
            neighbours[i].update(j for j in indices if j != i)
    degree = max(map(len, neighbours), default=0)
    order = list(range(len(candidates)))
    if strategy == 'score':
        order.sort(key=lambda i: (-candidates[i].get('euler_gain', 0),
                                 -candidates[i].get('normal_disc_saving', 0), i))
    selected, used = [], set()
    for i in order:
        budget.tick()
        if supports[i].isdisjoint(used):
            selected.append(i)
            used.update(supports[i])
    sites = [dict(tetrahedron=candidates[i]['tetrahedron'],
                  vertices=list(candidates[i]['vertices'])) for i in selected]
    return dict(selected_indices=selected, sites=sites,
                stats=dict(work=budget.work, candidates=len(candidates),
                           selected=len(selected), maximum_conflict_degree=degree))


def _selected_regions(prepared, sites, check):
    if type(sites) is not list:
        raise ValueError('sites must be a list of tetrahedron/vertices records')
    groups = _edge_occurrences(prepared, check)
    rows = prepared['tetrahedra']
    regions, roots, removed = [], set(), set()
    for site in sites:
        check()
        if type(site) is not dict or set(site) != {'tetrahedron', 'vertices'}:
            raise ValueError('a site must have exactly tetrahedron and vertices fields')
        t, vertices = site['tetrahedron'], site['vertices']
        if (type(t) is not int or not 0 <= t < len(rows)
                or type(vertices) is not list or len(vertices) != 2
                or any(type(v) is not int or not 0 <= v < 4 for v in vertices)
                or vertices[0] == vertices[1]):
            raise ValueError('invalid local degree-three-edge site')
        root = prepared['edge_roots'][_edge(t, *vertices)]
        if root in roots:
            raise ValueError('a central edge was selected more than once')
        roots.add(root)
        region = _collapse_region(rows, groups[root], check)
        if region is None:
            raise NormalOrbitError('selected edge is not a legal three-tetrahedron bipyramid')
        if not removed.isdisjoint(region):
            raise ValueError('selected 3--2 regions share a tetrahedron')
        removed.update(region)
        regions.append(region)
    # Dense input indices permit canonical ordering by one scan; sorting
    # arbitrary site addresses is not part of the layout complexity.
    by_first = {min(region): region for region in regions}
    regions = [by_first[t] for t in range(len(rows)) if t in by_first]
    return regions, removed


def _assemble(rows, regions, removed, check):
    """Transfer each external face by its full local vertex permutation."""
    survivors = [t for t in range(len(rows)) if t not in removed]
    index = {t: i for i, t in enumerate(survivors)}
    result = [[None] * 4 for _ in range(len(survivors) + 2 * len(regions))]
    ports = {}
    for t in survivors:
        check()
        for f in range(4):
            ports[t, f] = (index[t], f, (0, 1, 2, 3))
    for r, region in enumerate(regions):
        check()
        start = len(survivors) + 2 * r
        facets = {}
        for j, labels in enumerate(_NEW):
            for g in range(3):
                facets[tuple(sorted(labels[v] for v in range(4) if v != g))] = (j, g)
        for t, labels in region.items():
            for f in range(4):
                if labels[f] not in (3, 4):
                    continue
                key = tuple(sorted(labels[v] for v in range(4) if v != f))
                j, g = facets[key]
                mapping = tuple(g if v == f else _NEW[j].index(labels[v])
                                for v in range(4))
                ports[t, f] = (start + j, g, mapping)
        result[start][3] = dict(tetrahedron=start + 1, permutation=[0, 1, 2, 3])
        result[start + 1][3] = dict(tetrahedron=start, permutation=[0, 1, 2, 3])
    for (t, f), (target, g, mapping) in ports.items():
        check()
        old = rows[t][f]
        if old is None:
            continue
        u, p = old['tetrahedron'], old['permutation']
        address = (u, p[f])
        if address not in ports:
            raise NormalOrbitError('an external region face was paired with an internal face')
        other, _, target_map = ports[address]
        inverse = [mapping.index(v) for v in range(4)]
        permutation = [target_map[p[inverse[v]]] for v in range(4)]
        result[target][g] = dict(tetrahedron=other, permutation=permutation)
    return dict(tetrahedra=result), survivors


@_shield_callback
def pachner_32_batch(triangulation, sites, heights=None, *, max_work=None,
                     check=lambda: None):
    """Build and independently certify one simultaneous 3--2 batch.

    With heights, the certificate also checks class-preserving cocycle
    transport, all final normal coordinates, and both global cell jumps.
    The existing finite-manifold validator is called a constant three
    times (source discovery, then source and target replay), not per move.
    Its running time is not included in the linear layout-operation claim.
    """
    from .pachner_batch_verify import verify_pachner_32_batch

    budget = _Budget(check, max_work)
    prepared = _prepare(triangulation, budget.tick)
    h = (None if heights is None else
         _integer_heights(prepared, heights, budget.tick))
    regions, removed = _selected_regions(prepared, sites, budget.tick)
    after, survivors = _assemble(prepared['tetrahedra'], regions, removed, budget.tick)
    certificate = dict(schema='pachner-32-batch-v1',
                       regions=[_region_record(region) for region in regions])
    answer = dict(triangulation=after, certificate=certificate)
    if h is not None:
        final = [[x - h[t][0] for x in h[t]] for t in survivors]
        all_five, gain, saving = [], 0, 0
        for region in regions:
            budget.tick()
            five = _region_heights(region, h, budget.tick)
            all_five.append(five)
            score = bipyramid_cocycle_score(five)
            gain += score['euler_loss']
            saving += score['normal_disc_increase']
            for labels in _NEW:
                final.append([five[v] - five[labels[0]] for v in labels])
        coordinates = []
        for row in final:
            budget.tick()
            coordinates.append(local_coordinates(row))
        cocycle = dict(bipyramid_heights=all_five, heights=final,
                       coordinates=coordinates, euler_jump=gain,
                       normal_disc_jump=-saving)
        certificate['cocycle'] = cocycle
        answer.update(heights=deepcopy(final), coordinates=deepcopy(coordinates))
    if not verify_pachner_32_batch(triangulation, after, certificate,
                                  heights=heights, check=budget.tick):
        raise ArithmeticError('simultaneous Pachner replacement failed independent replay')
    answer['stats'] = dict(work=budget.work, moves=len(regions),
                          initial_tetrahedra=len(prepared['tetrahedra']),
                          remaining_tetrahedra=len(after['tetrahedra']),
                          replaced_tetrahedra=len(removed),
                          intermediate_triangulations=0, manifold_preparations=3)
    return answer
