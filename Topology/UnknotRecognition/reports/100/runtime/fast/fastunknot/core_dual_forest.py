"""Remove source core 3-handles by a cut-relative dual spanning forest.

The enclosing normal-parallelity checker must authenticate the supplied
geometric charts.  Dual incidences are then derived from source edge ends,
not accepted as arbitrary presentation data.  An endpoint facing a normal
sheet or the original boundary is represented by -1.  The cancellations
preserve all 0/1-handles, bundle ports, and surviving 2-handle attaching paths.

This finite preprocessing uses no normal-disc expansion, group reduction,
or manifold-recognition oracle.  Its independent replay is in
``core_dual_forest_verify``.
"""

from collections import deque

from .core_handlebody import _forest
from .normal_surface_geometry import _coordinates, _edge, _prepare


def _source_sides(geometry, check):
    prepared = _prepare(geometry['source'], check)
    analysed = _coordinates(prepared, geometry['coordinates'], check)
    core = geometry['core']
    boundary = {prepared['vertex_roots'][4 * t + v]
                for t, f in prepared['boundary_faces']
                for v in range(4) if v != f}
    groups = {}
    for t in range(len(prepared['tetrahedra'])):
        check()
        for v in range(4):
            root = prepared['vertex_roots'][4 * t + v]
            if root not in boundary:
                groups.setdefault(root, []).append([t, v])
    expected = [dict(id=i, vertex=root, link_triangles=flags)
                for i, (root, flags) in enumerate(sorted(groups.items()))]
    if core['handles3'] != expected:
        raise ArithmeticError('three-handles do not match source interior vertices')
    owner = {tuple(flag): h['id'] for h in core['handles3']
             for flag in h['link_triangles']}
    sides = []
    for index, handle in enumerate(core['handles2']):
        check()
        if handle['id'] != index or not handle['cycle']:
            raise ArithmeticError('source two-handle identity or cycle is invalid')
        flag = handle['cycle'][0]
        if flag['dimension'] != 0:
            raise ArithmeticError('source two-handle has no initial chamber flag')
        t = flag['tetrahedron']
        a, b = flag['local_edge']
        local = _edge(t, a, b)
        if prepared['edge_roots'][local] != handle['edge']:
            raise ArithmeticError('two-handle source edge does not match its flag')
        if prepared['edge_orientations'][local]:
            a, b = b, a
        first, last = owner.get((t, a), -1), owner.get((t, b), -1)
        weight = analysed['weights'][handle['edge']]
        rank = handle['rank']
        if weight == 0 and rank == 0:
            side = [first, last]
        elif weight > 0 and rank == 0:
            side = [first, -1]
        elif weight > 0 and rank == weight:
            side = [-1, last]
        else:
            raise ArithmeticError('source two-handle is not an endpoint gap')
        sides.append(side)
    return sides


def dual_forest_plan(sides, vertices, *, strategy='bfs', weights=None,
                     check=lambda: None):
    """Plan a rooted graph forest; graph data alone carry no topology verdict.

    ``max_weight`` maximizes the sum of the supplied nonnegative source-edge
    costs. The verifier need not repeat this optimization: it accepts every
    valid exposed-root elimination order. Vertices are 0,...,vertices-1;
    -1 is the distinguished exposed root, and loops retain both incidences.
    """
    check()
    if type(vertices) is not int or vertices < 0 or type(sides) is not list:
        raise ValueError('invalid dual graph containers')
    if strategy not in ('bfs', 'max_weight'):
        raise ValueError('strategy must be bfs or max_weight')
    if weights is None:
        weights = [0] * len(sides)
    if (type(weights) is not list or len(weights) != len(sides) or
            any(type(w) is not int or w < 0 for w in weights)):
        raise ValueError('dual edge costs must be nonnegative integers')
    for side in sides:
        check()
        if (type(side) is not list or len(side) != 2 or
                any(type(v) is not int or not -1 <= v < vertices for v in side)):
            raise ValueError('invalid dual edge endpoints')
    selected = set(range(len(sides)))
    if strategy == 'max_weight':
        parent = list(range(vertices + 1))

        def root(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v

        selected = set()
        for edge in sorted(range(len(sides)), key=lambda e: (-weights[e], e)):
            check()
            a, b = (root(v + 1) for v in sides[edge])
            if a != b:
                parent[max(a, b)] = min(a, b)
                selected.add(edge)
    adjacency = {v: [] for v in range(-1, vertices)}
    for number, (a, b) in enumerate(sides):
        check()
        if number in selected:
            adjacency[a].append((number, b))
            adjacency[b].append((number, a))
    visited, queue = {-1}, deque([-1])
    moves, removed, visits = [], set(), 0
    while queue:
        check()
        vertex = queue.popleft()
        for edge, neighbor in adjacency[vertex]:
            check()
            visits += 1
            if neighbor in visited:
                continue
            visited.add(neighbor)
            queue.append(neighbor)
            moves.append([neighbor, edge])
            removed.add(edge)
    return dict(cancellations=moves,
                unreachable_three_handles=sorted(set(adjacency) - visited),
                graph_incidence_visits=visits,
                removed_weight=sum(weights[e] for e in removed))


def core_dual_forest(geometry, *, strategy='bfs', check=lambda: None):
    """Produce a relative 2/3 cancellation certificate for authenticated charts.

    For every valid source in the established compact one-torus contract,
    every 3-handle is reachable from the exposed root: follow a source edge
    path to the boundary, stopping at its first positive normal weight.
    An unreachable component therefore reports INCONCLUSIVE rather than
    being silently erased.  Only the subsequent 1/2 recognition stage can
    establish a handlebody census. ``max_weight`` exactly minimizes the
    retained number of literal 1-handle passages outside the fixed canonical
    0/1 forest among all complete pure 2/3 forest cancellations. It does not
    optimize the success of later 1/2 cancellations.
    """
    check()
    core = geometry['core']
    sides = _source_sides(geometry, check)
    primal, _ = _forest(core, check)
    primal = set(primal)
    costs = []
    for handle in core['handles2']:
        check()
        costs.append(sum(flag['dimension'] == 1 and flag['handle'] not in primal
                         for flag in handle['cycle']))
    plan = dual_forest_plan(sides, len(core['handles3']), strategy=strategy,
                            weights=costs, check=check)
    moves = plan['cancellations']
    removed = {edge for _, edge in moves}
    stats = dict(three_handles=len(core['handles3']), strategy=strategy,
                 source_two_handles=len(sides),
                 graph_incidence_visits=plan['graph_incidence_visits'],
                 cancellations=len(moves), primal_forest_edges=len(primal),
                 initial_raw_passages=sum(costs),
                 removed_raw_passages=plan['removed_weight'],
                 retained_raw_passages=sum(costs) - plan['removed_weight'])
    if plan['unreachable_three_handles']:
        return dict(status='INCONCLUSIVE', reason='unexposed_dual_component',
                    unreachable_three_handles=plan['unreachable_three_handles'],
                    stats=stats)
    survivors = [i for i in range(len(sides)) if i not in removed]
    reduced = dict(core, handles2=[dict(core['handles2'][old], id=new)
                                  for new, old in enumerate(survivors)],
                   handles3=[])
    proof = dict(schema='normal-core-dual-forest-v1', source_sides=sides,
                 cancellations=moves, surviving_two_handles=survivors)
    check()
    return dict(status='COMPLETE', core=reduced, certificate=proof, stats=stats,
                trust='relative geometric 2/3 cancellation; authenticated source charts required')
