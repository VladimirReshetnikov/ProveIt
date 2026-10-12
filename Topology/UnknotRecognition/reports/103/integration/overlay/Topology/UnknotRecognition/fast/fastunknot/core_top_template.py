"""One source vertex tree specializes to every admissible normal cut.

The reusable object contains only source vertex and edge labels.  Positive
edge weights break a parent edge at the normal surface; its child end then
roots directly on the new boundary.  Zero-weight edges use the parent that
was already rooted.  This is a planner, not a source geometry verifier.
Its specialized certificates are checked by core_top_reduction_verify.
"""

from collections import deque
import hashlib
import json

from .core_top_reduction import source_core_top_incidence
from .normal_surface_geometry import _prepare, _EDGES


def _source_hash(triangulation):
    return hashlib.sha256(json.dumps(triangulation, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def _vertex_data(prepared, check):
    boundary = {prepared['vertex_roots'][4*t+v]
                for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    ends = {}
    for edge in sorted(set(prepared['edge_roots'])):
        check()
        t, j = divmod(edge, 6)
        ends[edge] = tuple(prepared['vertex_roots'][4*t+v] for v in _EDGES[j])
    vertices = set(prepared['vertex_roots'])
    return boundary, vertices, ends


def compile_source_top_tree(triangulation, *, check=lambda: None):
    """Compile a boundary-rooted source tree, independent of normal coordinates."""
    check()
    prepared = _prepare(triangulation, check)
    boundary, vertices, ends = _vertex_data(prepared, check)
    adjacency = {v: [] for v in vertices}
    for edge, (a, b) in ends.items():
        check()
        if a != b:
            adjacency[a].append((b, edge))
            adjacency[b].append((a, edge))
    seen, queue = set(boundary), deque(sorted(boundary))
    parents = []
    while queue:
        check()
        parent = queue.popleft()
        for vertex, edge in adjacency[parent]:
            if vertex in seen:
                continue
            seen.add(vertex)
            queue.append(vertex)
            parents.append(dict(vertex=vertex, parent=parent, edge=edge))
    if seen != vertices:
        raise ArithmeticError('source vertex graph does not reach the boundary')
    return dict(schema='source-core-top-tree-v1',
                source_sha256=_source_hash(triangulation), parents=parents)


def verify_source_top_tree(triangulation, template, *, check=lambda: None):
    """Validate a supplied tree by parent precedence and exact source edges.

    This never calls the BFS compiler.  Any valid boundary-rooted tree order
    is accepted, so it can also check externally chosen source templates.
    """
    check()
    if (type(template) is not dict or
            set(template) != {'schema', 'source_sha256', 'parents'} or
            template['schema'] != 'source-core-top-tree-v1' or
            template['source_sha256'] != _source_hash(triangulation) or
            type(template['parents']) is not list):
        return False
    prepared = _prepare(triangulation, check)
    boundary, vertices, ends = _vertex_data(prepared, check)
    reached, used = set(boundary), set()
    for record in template['parents']:
        check()
        if (type(record) is not dict or set(record) != {'vertex', 'parent', 'edge'} or
                any(type(v) is not int for v in record.values())):
            return False
        vertex, parent, edge = record['vertex'], record['parent'], record['edge']
        if (vertex not in vertices or vertex in reached or parent not in reached or
                edge not in ends or edge in used or
                sorted(ends[edge]) != sorted((vertex, parent))):
            return False
        reached.add(vertex)
        used.add(edge)
    check()
    return reached == vertices


def specialize_source_top_tree(triangulation, coordinates, geometry, template,
                               *, check=lambda: None):
    """Return a normal-core-top-reduction-v1 proof for this supplied cut.

    Source and coordinate validation are retained at this public entry point.
    The enclosing cut verifier independently checks the specialized proof;
    correctness does not depend on trusting this planner or its template.
    """
    check()
    if not verify_source_top_tree(triangulation, template, check=check):
        raise ValueError('invalid source top-handle tree')
    incidence = source_core_top_incidence(triangulation, coordinates, geometry,
                                          check=check)
    by_vertex = {v: i for i, v in enumerate(incidence['three_handles'])}
    by_edge = {}
    for edge in incidence['two_handles']:
        check()
        by_edge.setdefault(edge['edge'], []).append(edge)
    moves, selected = [], set()
    for record in template['parents']:
        check()
        vertex = by_vertex[record['vertex']]
        candidates = by_edge[record['edge']]
        if len(candidates) == 1:
            chosen = candidates[0]
        else:
            candidates = [edge for edge in candidates if vertex in edge['ends']]
            if len(candidates) != 1:
                raise ArithmeticError('a source tree edge has ambiguous child end')
            chosen = candidates[0]
        if chosen['id'] in selected:
            raise ArithmeticError('source tree specialization reused a two-handle')
        moves.append([chosen['id'], vertex])
        selected.add(chosen['id'])
    return dict(schema='normal-core-top-reduction-v1',
                input_sha256=incidence['input_sha256'], moves=moves,
                surviving_two_handles=[edge['id'] for edge in incidence['two_handles']
                                       if edge['id'] not in selected])
