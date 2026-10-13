"""Independent replay of inverse boundary layering on a one-vertex source.

The successor must reconstruct the original by Jaco--Rubinstein layering
along an oriented edge shared by two distinct boundary triangles. Identified
quadrilateral sides are allowed; an embedded attaching disc is not assumed.
This preserves the compact manifold, but supplies no standalone knot verdict.
No simplifier, layering producer, search backend, or research code is imported.
"""

from hashlib import sha256
import json

from .normal_surface_geometry import _prepare, _EDGES


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def verify_boundary_unlayering(source, certificate, *, check=lambda: None):
    """Check a source-bound, densely relabelled single-tetrahedron removal.

    Malformed or unsupported packets return False. Every caller exception,
    including exceptions raised inside manifold validation, propagates with
    its original identity. Both sources must have one vertex and torus boundary.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None

    try:
        return _verify(source, certificate, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _verify(source, certificate, check):
    check()
    try:
        fields = {'schema', 'source_sha256', 'tetrahedron', 'successor'}
        if (type(certificate) is not dict or set(certificate) != fields or
                type(certificate['schema']) is not str or
                certificate['schema'] != 'normal-boundary-unlayer-v1' or
                type(certificate['source_sha256']) is not str or
                type(certificate['tetrahedron']) is not int):
            return False
        original = _prepare(source, check)
        count = len(original['tetrahedra'])
        removed = certificate['tetrahedron']
        if (count < 2 or not 0 <= removed < count or
                original['vertices'] != 1 or len(original['boundary_faces']) != 2 or
                any(t != removed for t, _ in original['boundary_faces'])):
            return False
        check()
        digest = sha256(json.dumps(source, sort_keys=True,
                                   separators=(',', ':')).encode('utf-8')).hexdigest()
        if certificate['source_sha256'] != digest:
            return False
        joins = [(face, record) for face, record in
                 enumerate(original['tetrahedra'][removed]) if record is not None]
        if len(joins) != 2 or any(record['tetrahedron'] == removed for _, record in joins):
            return False
        attached = [(record['tetrahedron'], record['permutation'][face])
                    for face, record in joins]
        if len(set(attached)) != 2:
            return False

        successor = _prepare(certificate['successor'], check)
        if (len(successor['tetrahedra']) != count-1 or
                successor['vertices'] != 1 or len(successor['boundary_faces']) != 2):
            return False
        survivors = [t for t in range(count) if t != removed]
        index = {old: new for new, old in enumerate(survivors)}
        exposed = {(index[t], face) for t, face in attached}
        if exposed != set(successor['boundary_faces']):
            return False

        # Only the two reciprocal attachment records may become boundary.
        # All local vertex labels persist, and surviving tetrahedra keep order.
        for new, old in enumerate(survivors):
            check()
            for before, after in zip(original['tetrahedra'][old],
                                     successor['tetrahedra'][new]):
                if before is None or before['tetrahedron'] == removed:
                    if after is not None:
                        return False
                elif (after is None or after['tetrahedron'] != index[before['tetrahedron']] or
                      after['permutation'] != before['permutation']):
                    return False

        # The two attaching maps must agree on the shared edge as an
        # oriented global edge, even when both ends are the unique vertex.
        shared = sorted(set(range(4))-{face for face, _ in joins})
        interface = []
        for _, record in joins:
            check()
            a, b = (record['permutation'][v] for v in shared)
            local = 6*index[record['tetrahedron']]+_EDGES.index(tuple(sorted((a, b))))
            interface.append((successor['edge_roots'][local],
                              successor['edge_orientations'][local] ^ int(a > b)))
        if interface[0] != interface[1]:
            return False
        old_diagonal = interface[0][0]
        if old_diagonal not in successor['boundary_incidence']:
            return False

        # Compare independently rebuilt edge classes on every surviving
        # incidence: adding this tetrahedron must not merge old edge classes
        # or reverse the identification of any old edge's oriented ends.
        edge_map = {}
        for new, old in enumerate(survivors):
            check()
            for edge in range(6):
                small, large = 6*new+edge, 6*old+edge
                root = successor['edge_roots'][small]
                image = (original['edge_roots'][large],
                         successor['edge_orientations'][small] ^
                         original['edge_orientations'][large])
                if root in edge_map and edge_map[root] != image:
                    return False
                edge_map[root] = image
        images = {root for root, _ in edge_map.values()}
        if len(images) != len(edge_map):
            return False
        new_edge_vertices = tuple(sorted(face for face, _ in joins))
        new_diagonal = original['edge_roots'][
            6*removed+_EDGES.index(new_edge_vertices)]
        if (original['edges'] != successor['edges']+1 or
                set(original['endpoints'])-images != {new_diagonal}):
            return False
        old_boundary = {edge_map[edge][0] for edge in successor['boundary_incidence']}
        expected_boundary = (old_boundary-{edge_map[old_diagonal][0]}) | {new_diagonal}
        check()
        return set(original['boundary_incidence']) == expected_boundary
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
