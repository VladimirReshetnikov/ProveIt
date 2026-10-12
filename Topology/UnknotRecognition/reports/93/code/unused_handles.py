"""Source-bound unused-handle decomposition and initial empty-pattern cores.

The generic producer/checker authenticate geometric decomposition only.
The topological interpretation of Euler-characteristic-one pieces as balls
requires irreducibility.  The diagram wrapper authenticates that hypothesis
using the maintained canonical-exterior checker; no user-supplied Boolean
can enable it.

The cancellation scheduler below is adapted from ProveIt's maintained
fastunknot/source_handle_reduction.py at the pinned source checkpoint.  It
has the same queue order, but stops before boundary-period construction.
Its cancellation certificates are also accepted by the unchanged native
checker.  The standalone checker adapts that checker's raw-cell replay in
one pass, then independently constructs the quotient by breadth-first search.
Only the quotient, budget interpretation, and compiler wrapper are new.

Requires the pinned ProveIt Topology/UnknotRecognition/fast on PYTHONPATH.
No maintained file or recognizer default is modified.
"""

from collections import Counter, deque

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _fingerprint
from fastunknot.source_handle_reduction import _source_handles


def _exact_equal(left, right):
    """Structural equality that does not identify Boolean and integer labels."""
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(
            _exact_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            _exact_equal(a, b) for a, b in zip(left, right)
        )
    return left == right


def _incidence_reduction(triangulation, max_moves, check):
    """The native geometric queue scheduler, without cocore cohomology."""
    prepared = _prepare(triangulation, check)
    handles = _source_handles(prepared, check)
    faces = set(range(len(handles['one_handles'])))
    edges = {edge['id']: edge for edge in handles['two_handles']}
    alive = set(edges)
    vertices = set(handles['three_handles'])
    vertex_edges = {vertex: [] for vertex in vertices}
    for edge in handles['two_handles']:
        for vertex in set(edge['ends']):
            if vertex in vertices:
                vertex_edges[vertex].append(edge['id'])
    queue = deque(
        edge['id'] for edge in handles['two_handles']
        if sum(vertex in vertices for vertex in edge['ends']) == 1
    )
    moves = []
    while vertices:
        check()
        if not queue:
            raise ArithmeticError('interior handles do not reach the boundary')
        edge = queue.popleft()
        if edge not in alive:
            continue
        ends = [vertex for vertex in edges[edge]['ends'] if vertex in vertices]
        if len(ends) != 1:
            continue
        if max_moves is not None and len(moves) >= max_moves:
            return None
        vertex = ends[0]
        moves.append(dict(kind='cancel_23', two_handle=edge, three_handle=vertex))
        alive.remove(edge)
        vertices.remove(vertex)
        for other in vertex_edges[vertex]:
            check()
            if other in alive and sum(v in vertices for v in edges[other]['ends']) == 1:
                queue.append(other)
    occurrences = {
        edge: Counter(item['one_handle'] for item in edges[edge]['attaching_cycle'])
        for edge in alive
    }
    incidence = {face: {} for face in faces}
    degree = [0] * len(faces)
    for edge, counts in occurrences.items():
        for face, count in counts.items():
            incidence[face][edge] = count
            degree[face] += count
    queue = deque(face for face in sorted(faces) if degree[face] == 1)
    while queue:
        check()
        face = queue.popleft()
        if face not in faces or degree[face] != 1:
            continue
        if max_moves is not None and len(moves) >= max_moves:
            return None
        edge = next(iter(incidence[face]))
        moves.append(dict(kind='cancel_12', one_handle=face, two_handle=edge))
        faces.remove(face)
        alive.remove(edge)
        for other, count in occurrences[edge].items():
            check()
            del incidence[other][edge]
            degree[other] -= count
            if other in faces and degree[other] == 1:
                queue.append(other)
    remaining = dict(one_handles=sorted(faces), two_handles=sorted(alive), three_handles=[])
    summary = dict(
        initial_handle_counts=[handles['zero_handles'], len(handles['one_handles']),
                               len(handles['two_handles']), len(handles['three_handles'])],
        remaining_handle_counts=[handles['zero_handles'], len(faces), len(alive), 0],
        characteristic_zero_handle_indices=[
            dict(one_handle=face, index=-4 + 2 * degree[face], multiplicity=2)
            for face in sorted(faces)
        ],
    )
    zero = _coordinates(prepared, [[0] * 7 for _ in prepared['tetrahedra']], check)
    proof = dict(
        schema='source-handle-reduction-v1',
        input_sha256=_fingerprint(triangulation, zero, check),
        boundary_pattern='empty', moves=moves, remaining=remaining,
        summary=summary, compressing_disc=None,
    )
    return handles, proof, degree


def _producer_components(handles, reduction, degree, check):
    number = handles['zero_handles']
    parent = list(range(number))
    sizes = [1] * number

    def root(vertex):
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    alive = reduction['remaining']['one_handles']
    for face in alive:
        check()
        if degree[face]:
            a, b = handles['one_handles'][face]['ends']
            a, b = root(a), root(b)
            if a != b:
                if sizes[a] < sizes[b]:
                    a, b = b, a
                parent[b] = a
                sizes[a] += sizes[b]
    blocks = {}
    for vertex in range(number):
        blocks.setdefault(root(vertex), []).append(vertex)
    components = [dict(id=i, zero_handles=vertices, one_handles=[], two_handles=[])
                  for i, vertices in enumerate(sorted(blocks.values()))]
    owner = {vertex: component['id'] for component in components
             for vertex in component['zero_handles']}
    unused = []
    for face in alive:
        check()
        a, b = handles['one_handles'][face]['ends']
        if degree[face]:
            if owner[a] != owner[b]:
                raise ArithmeticError('used handle crosses quotient components')
            components[owner[a]]['one_handles'].append(face)
        else:
            unused.append(dict(one_handle=face, ends=[owner[a], owner[b]]))
    edge_map = {edge['id']: edge for edge in handles['two_handles']}
    for edge in reduction['remaining']['two_handles']:
        check()
        carriers = {owner[sector['tetrahedron']] for sector in edge_map[edge]['sectors']}
        if len(carriers) != 1:
            raise ArithmeticError('two-handle crosses unused-handle components')
        components[carriers.pop()]['two_handles'].append(edge)
    for component in components:
        component['euler_characteristic'] = (
            len(component['zero_handles']) - len(component['one_handles'])
            + len(component['two_handles'])
        )
    return dict(components=components, unused_handles=unused,
                cycle_rank=len(unused) - len(components) + 1)


def _torus_case(decomposition):
    components = decomposition['components']
    chi = [component['euler_characteristic'] for component in components]
    beta = decomposition['cycle_rank']
    if beta == 1 and all(value == 1 for value in chi):
        return 'cycle', None
    zeros = [component['id'] for component in components
             if component['euler_characteristic'] == 0]
    if beta == 0 and len(zeros) == 1 and all(value in (0, 1) for value in chi):
        return 'unique_core', zeros[0]
    return 'outside_irreducible_signature', None


def _check_local_characteristic(raw, one, two, alive, edges, degree, check):
    """Verify the source-local K4 invariant needed for robust admissibility.

    Port occurrences are local tetrahedron facets, even when two are ends
    of the same global one-handle.  Source local edge occurrences, not
    abelianized relator coefficients, give characteristic strips.
    """
    ports = [dict() for _ in raw['handles0']]
    strips = [set() for _ in raw['handles0']]
    for face in alive:
        if not degree[face]:
            continue
        record = one[face]
        for tetrahedron, local_face in (
            (record['tetrahedron'], record['face']),
            (record['target_tetrahedron'], record['target_face']),
        ):
            check()
            if local_face in ports[tetrahedron]:
                return False
            ports[tetrahedron][local_face] = face
    for edge in edges:
        for sector in two[edge]['cycle']:
            check()
            if sector['dimension'] != 0:
                continue
            tetrahedron = sector['tetrahedron']
            ends = tuple(face for face in range(4) if face not in sector['local_edge'])
            if len(ends) != 2 or any(face not in ports[tetrahedron] for face in ends):
                return False
            if ends in strips[tetrahedron]:
                return False
            strips[tetrahedron].add(ends)
    for tetrahedron, local_ports in enumerate(ports):
        if not local_ports:
            if strips[tetrahedron]:
                return False
            continue
        adjacency = {face: [] for face in local_ports}
        for a, b in strips[tetrahedron]:
            adjacency[a].append(b)
            adjacency[b].append(a)
        for face, global_face in local_ports.items():
            if len(adjacency[face]) != degree[global_face] or len(adjacency[face]) < 2:
                return False
        reached = {next(iter(local_ports))}
        queue = deque(reached)
        while queue:
            check()
            for other in adjacency[queue.popleft()]:
                if other not in reached:
                    reached.add(other)
                    queue.append(other)
        if len(reached) != len(local_ports):
            return False
    return True


def decompose_unused_handles(triangulation, *, max_moves=None, check=lambda: None):
    """Produce exact cut components with no ball or knot verdict on raw sources.

    A finite supported orientable connected torus-boundary triangulation is
    required by the existing native source validator.  Reducible inputs are
    allowed.  In particular, 'torus_case' is an arithmetic case name and does
    not authenticate irreducibility.  INCONCLUSIVE emits no certificate.
    """
    check()
    if max_moves is not None and (type(max_moves) is not int or max_moves < 0):
        raise ValueError('max_moves must be a nonnegative integer or None')
    reduced = _incidence_reduction(triangulation, max_moves, check)
    if reduced is None:
        return dict(status='INCONCLUSIVE', reason='source handle move cap')
    handles, proof, degree = reduced
    decomposition = _producer_components(handles, proof, degree, check)
    case, core = _torus_case(decomposition)
    certificate = dict(
        schema='unused-handles-v1', reduction_certificate=proof,
        decomposition=decomposition, torus_case=case, core_component=core,
    )
    check()
    return dict(status='DECOMPOSED', reduction_certificate=proof,
                decomposition=decomposition, torus_case=case,
                core_component=core, certificate=certificate)


def verify_unused_handle_certificate(triangulation, certificate, *, max_moves=None,
                                     check=lambda: None):
    """Independent geometry and BFS replay, without producer scheduling/union-find.

    Acceptance authenticates the stated geometric disc-cut decomposition.
    It does not authenticate irreducibility or identify arbitrary chi=1
    manifolds as balls.
    """
    check()
    if max_moves is not None and (type(max_moves) is not int or max_moves < 0):
        raise ValueError('max_moves must be a nonnegative integer or None')
    fields = {'schema', 'reduction_certificate', 'decomposition', 'torus_case',
              'core_component'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if certificate['schema'] != 'unused-handles-v1':
        return False
    reduction = certificate['reduction_certificate']
    reduction_fields = {'schema', 'input_sha256', 'boundary_pattern', 'moves',
                        'remaining', 'summary', 'compressing_disc'}
    if type(reduction) is not dict or set(reduction) != reduction_fields:
        return False
    if reduction['schema'] != 'source-handle-reduction-v1':
        return False
    if reduction['boundary_pattern'] != 'empty' or reduction['compressing_disc'] is not None:
        return False
    moves = reduction['moves']
    if type(moves) is not list or max_moves is not None and len(moves) > max_moves:
        return False
    prepared = _prepare(triangulation, check)
    zero = _coordinates(prepared, [[0] * 7 for _ in prepared['tetrahedra']], check)
    if reduction['input_sha256'] != _fingerprint(triangulation, zero, check):
        return False
    raw = _reference_parallelity(prepared, zero, check)['core']
    one = {record['id']: record for record in raw['handles1']}
    two = {record['edge']: record for record in raw['handles2']}
    surviving_faces = set(one)
    surviving_edges = set(two)
    surviving_vertices = {record['vertex'] for record in raw['handles3']}
    # Count genuine attaching occurrences in independently reconstructed
    # source cells.  Every removed two-handle decrements its row once, so
    # replay does not rescan every remaining attaching curve at every move.
    row_counts = {}
    live_degree = Counter()
    for edge, record in two.items():
        counts = Counter()
        for sector in record['cycle']:
            check()
            if sector['dimension'] == 1:
                counts[sector['handle']] += 1
        row_counts[edge] = counts
        live_degree.update(counts)

    def remove_row(edge):
        surviving_edges.remove(edge)
        for face, count in row_counts[edge].items():
            check()
            live_degree[face] -= count

    # A unit algebraic coefficient is never sufficient: live_degree counts
    # both orientations positively, including repeated occurrences.
    for move in moves:
        check()
        if type(move) is not dict:
            return False
        if move.get('kind') == 'cancel_23':
            if set(move) != {'kind', 'two_handle', 'three_handle'}:
                return False
            edge, vertex = move['two_handle'], move['three_handle']
            if type(edge) is not int or type(vertex) is not int:
                return False
            if edge not in surviving_edges or vertex not in surviving_vertices:
                return False
            contacts = [v for v in prepared['endpoints'][edge] if v in surviving_vertices]
            if contacts != [vertex]:
                return False
            remove_row(edge)
            surviving_vertices.remove(vertex)
        elif move.get('kind') == 'cancel_12':
            if surviving_vertices or set(move) != {'kind', 'one_handle', 'two_handle'}:
                return False
            face, edge = move['one_handle'], move['two_handle']
            if type(face) is not int or type(edge) is not int:
                return False
            if face not in surviving_faces or edge not in surviving_edges:
                return False
            if live_degree[face] != 1 or row_counts[edge][face] != 1:
                return False
            surviving_faces.remove(face)
            remove_row(edge)
        else:
            return False
    if surviving_vertices:
        return False
    alive = sorted(surviving_faces)
    edges = sorted(surviving_edges)
    degree = Counter()
    for edge in edges:
        for sector in two[edge]['cycle']:
            check()
            if sector['dimension'] == 1:
                if sector['handle'] not in surviving_faces:
                    return False
                degree[sector['handle']] += 1
    expected_remaining = dict(one_handles=alive, two_handles=edges, three_handles=[])
    expected_summary = dict(
        initial_handle_counts=[len(raw[f'handles{i}']) for i in range(4)],
        remaining_handle_counts=[len(raw['handles0']), len(alive), len(edges), 0],
        characteristic_zero_handle_indices=[
            dict(one_handle=face, index=-4 + 2 * degree[face], multiplicity=2)
            for face in alive
        ],
    )
    if not _exact_equal(reduction['remaining'], expected_remaining):
        return False
    if not _exact_equal(reduction['summary'], expected_summary):
        return False
    if any(degree[face] == 1 for face in alive):
        return False  # Initial admissibility requires the complete leaf closure.
    if not _check_local_characteristic(raw, one, two, alive, edges, degree, check):
        return False
    adjacency = [[] for _ in raw['handles0']]
    for face in alive:
        check()
        if degree[face]:
            a, b = one[face]['ends']
            adjacency[a].append(b)
            adjacency[b].append(a)
    owner = {}
    components = []
    for start in range(len(adjacency)):
        check()
        if start in owner:
            continue
        index = len(components)
        queue = deque([start])
        owner[start] = index
        vertices = []
        while queue:
            check()
            vertex = queue.popleft()
            vertices.append(vertex)
            for other in adjacency[vertex]:
                if other not in owner:
                    owner[other] = index
                    queue.append(other)
        components.append(dict(id=index, zero_handles=sorted(vertices),
                               one_handles=[], two_handles=[]))
    unused = []
    for face in alive:
        a, b = one[face]['ends']
        if degree[face]:
            if owner[a] != owner[b]:
                return False
            components[owner[a]]['one_handles'].append(face)
        else:
            unused.append(dict(one_handle=face, ends=[owner[a], owner[b]]))
    for edge in edges:
        carriers = {owner[sector['handle']] for sector in two[edge]['cycle']
                    if sector['dimension'] == 0}
        if len(carriers) != 1:
            return False
        components[carriers.pop()]['two_handles'].append(edge)
    for component in components:
        component['euler_characteristic'] = sum(
            sign * len(component[key]) for sign, key in
            ((1, 'zero_handles'), (-1, 'one_handles'), (1, 'two_handles'))
        )
    quotient = [[] for _ in components]
    for edge in unused:
        a, b = edge['ends']
        quotient[a].append(b)
        quotient[b].append(a)
    reached = {0}
    queue = deque([0])
    while queue:
        check()
        for other in quotient[queue.popleft()]:
            if other not in reached:
                reached.add(other)
                queue.append(other)
    if len(reached) != len(components):
        return False
    beta = len(unused) - len(components) + 1
    expected = dict(components=components, unused_handles=unused, cycle_rank=beta)
    if not _exact_equal(certificate['decomposition'], expected):
        return False
    zero_ids = [c['id'] for c in components if c['euler_characteristic'] == 0]
    if beta == 1 and all(c['euler_characteristic'] == 1 for c in components):
        case, core = 'cycle', None
    elif beta == 0 and len(zero_ids) == 1 and all(
        c['euler_characteristic'] in (0, 1) for c in components
    ):
        case, core = 'unique_core', zero_ids[0]
    else:
        case, core = 'outside_irreducible_signature', None
    check()
    return certificate['torus_case'] == case and _exact_equal(
        certificate['core_component'], core
    )


def compile_diagram_initial_core(diagram, *, max_moves=None, check=lambda: None):
    """Compile an authenticated diagram exterior to a disc verdict or a core.

    UNKNOT is a positive certificate.  ADMISSIBLE_CORE is an intermediate
    handle presentation and is never a negative knot verdict.  The empty
    pattern is part of the contract; this routine is not a later-hierarchy
    pattern transporter and does not produce a retriangulation.
    """
    source = Diagram.from_pd(diagram.pd)
    raw = diagram_exterior(source, check=check)
    result = decompose_unused_handles(raw, max_moves=max_moves, check=check)
    if result['status'] == 'INCONCLUSIVE':
        return result
    case = result['torus_case']
    if case == 'outside_irreducible_signature':
        raise ArithmeticError('authenticated exterior violates the genus budget')
    outcome = 'UNKNOT' if case == 'cycle' else 'ADMISSIBLE_CORE'
    certificate = dict(
        schema='diagram-initial-core-v1', input_pd=[list(row) for row in source.pd],
        triangulation=raw, unused_handle_certificate=result['certificate'],
        outcome=outcome,
    )
    core = None
    if outcome == 'ADMISSIBLE_CORE':
        core = result['decomposition']['components'][result['core_component']]
    return dict(status=outcome, retained_core=core,
                decomposition=result['decomposition'], certificate=certificate)


def verify_diagram_initial_core(diagram, certificate, *, check=lambda: None):
    """Authenticate knot-exterior provenance before using irreducibility."""
    check()
    fields = {'schema', 'input_pd', 'triangulation', 'unused_handle_certificate', 'outcome'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if certificate['schema'] != 'diagram-initial-core-v1':
        return False
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return False
    if not _exact_equal(certificate['input_pd'], [list(row) for row in source.pd]):
        return False
    raw = certificate['triangulation']
    if not verify_diagram_exterior(source, raw, check=check):
        return False
    proof = certificate['unused_handle_certificate']
    if not verify_unused_handle_certificate(raw, proof, check=check):
        return False
    if proof['torus_case'] == 'cycle':
        expected = 'UNKNOT'
    elif proof['torus_case'] == 'unique_core':
        expected = 'ADMISSIBLE_CORE'
    else:
        return False
    check()
    return certificate['outcome'] == expected
