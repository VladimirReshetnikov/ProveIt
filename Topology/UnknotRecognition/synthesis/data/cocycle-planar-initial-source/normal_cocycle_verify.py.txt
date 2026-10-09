"""Source-bound connectedness and Euler checks for coherent cocycle surfaces.

No cocycle elimination, flow search or interval-orbit producer is imported.
Rank one comes from the authenticated knot exterior. Integral primitivity
is checked after an independently chosen tree gauge, never from the gcd of
ungauged edge values. Connectivity follows from either a zero spanning tree
or a checked minimum-span witness; an arbitrary primitive surface need not
be connected.
"""
from math import gcd

from .diagram import Diagram, DiagramError
from .diagram_exterior_verify import verify_diagram_exterior
from .cocycle_span_verify import verify_cocycle_span
from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, NormalOrbitError


def _primitive_cochain(prepared, heights, zero_tree, check):
    """Return global signed values for a primitive class, or None.

    Height differences already close around each local triangle. Checking
    every signed edge occurrence makes these one global integral cocycle.
    A breadth-first tree is independent of the producer's union-find tree.
    """
    endpoints, values = {}, {}
    for t, row in enumerate(heights):
        check()
        for j, (a, b) in enumerate(_EDGES):
            edge = 6*t+j
            root = prepared['edge_roots'][edge]
            pair = (prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b])
            value = row[b]-row[a]
            if prepared['edge_orientations'][edge]:
                pair, value = pair[::-1], -value
            if root in values and (values[root] != value or endpoints[root] != pair):
                return None
            endpoints[root], values[root] = pair, value
    adjacency = {v: [] for v in prepared['vertex_roots']}
    for edge, (a, b) in endpoints.items():
        check()
        value = values[edge]
        if not zero_tree or value == 0:
            adjacency[a].append((b, value))
            adjacency[b].append((a, -value))
    start = min(adjacency)
    potential, queue = {start: 0}, [start]
    for vertex in queue:
        check()
        for other, value in adjacency[vertex]:
            check()
            if other not in potential:
                potential[other] = potential[vertex]+value
                queue.append(other)
    if len(potential) != len(adjacency):
        return None
    common = 0
    for edge, (a, b) in endpoints.items():
        check()
        common = gcd(common, values[edge]-potential[b]+potential[a])
    return values if common == 1 else None


def inspect_cocycle_certificate(diagram, certificate, *, check=lambda: None):
    """Return certified connected-surface data, or None for an invalid proof.

    A valid certificate with Euler characteristic other than one describes
    a restricted candidate miss, not a negative knot certificate.
    """
    check()
    fields = {'schema', 'input_pd', 'triangulation', 'heights', 'coordinates', 'span_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'diagram-cocycle-disc-v1'):
        return None
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return None
    if not certificate_equal(certificate['input_pd'], [list(row) for row in source.pd]):
        return None
    raw = certificate['triangulation']
    if not verify_diagram_exterior(source, raw, check=check):
        return None
    try:
        prepared = _prepare(raw, check)
        analysed = _coordinates(prepared, certificate['coordinates'], check)
    except NormalOrbitError:
        return None
    supplied = certificate['heights']
    if type(supplied) is not list or len(supplied) != len(prepared['tetrahedra']):
        return None
    heights = []
    for row in supplied:
        check()
        if type(row) is not list or len(row) != 4:
            return None
        try:
            heights.append([encoded_integer(value) for value in row])
        except ValueError:
            return None
    span = certificate['span_certificate']
    values = _primitive_cochain(prepared, heights, span is None, check)
    if values is None:
        return None
    if span is None:
        # Admissibility plus all six edge weights uniquely determines each
        # local normal vector; no producer gap reconstruction is trusted.
        for edge, value in values.items():
            check()
            if analysed['weights'][edge] != abs(value):
                return None
    else:
        vertices = [prepared['vertex_roots'][4*t:4*t+4] for t in range(len(heights))]
        if (not verify_cocycle_span(vertices, heights, span, check=check)
                or not certificate_equal(span['coordinates'], analysed['rows'])):
            return None
    check()
    return dict(components=1, orientable_components=1,
                euler_characteristic=analysed['euler_characteristic'],
                normal_pieces=analysed['normal_disks'],
                compressing_discs=int(analysed['euler_characteristic'] == 1),
                connectivity='zero-tree' if span is None else 'minimum-span')
