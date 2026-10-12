"""Source-authenticated chamber graphs for labelled normal components.

The input is one embedded normal surface and one representative disc per
component.  Component labels are checked by an exact scalar orbit census;
the orientation double must have twice as many components.  A second
scalar census locates the two sides of every component in the actual cut.
Normal copies are never enumerated.  This is an observer, not a knot test.
"""

from .interval_orbits import count_orbits
from .normal_cut_complement import _chamber_system
from .normal_surface_geometry import (
    _arc_system, _coordinates, _edge, _fingerprint, _prepare,
)
from .integer_codec import encoded_integer
from .weighted_orbits import weighted_orbit_histogram


def _representatives(rows, supplied, check):
    if supplied is None:
        supplied = []
        for t, row in enumerate(rows):
            check()
            present = next((c for c, n in enumerate(row) if n), None)
            if present is not None:
                supplied = [dict(tetrahedron=t, column=present, rank=0)]
                break
    if type(supplied) is not list:
        raise ValueError('representatives must be a list of normal disc records')
    result = []
    for record in supplied:
        check()
        if type(record) is not dict or set(record) != {'tetrahedron', 'column', 'rank'}:
            raise ValueError('a representative requires tetrahedron, column and rank')
        t, c, r = (encoded_integer(record[key]) for key in ('tetrahedron', 'column', 'rank'))
        if not (0 <= t < len(rows) and 0 <= c < 7 and 0 <= r < rows[t][c]):
            raise ValueError('normal disc representative is outside the source')
        result.append(dict(tetrahedron=t, column=c, rank=r))
    return result


def _markers(prepared, analysed, representatives, check):
    """Locate an edge vertex and both adjacent chambers of each marked disc."""
    rows = analysed['rows']
    offsets, total = {}, 0
    for edge, weight in sorted(analysed['weights'].items()):
        check()
        offsets[edge] = total
        total += weight
    layout, size = [], 0
    for row in rows:
        check()
        quad = sum(row[4:])
        typ = next((c - 4 for c in range(4, 7) if row[c]), None)
        chain = size
        size += quad + 1
        arms = []
        for value in row[:4]:
            arms.append(size)
            size += value
        layout.append((chain, arms, quad, typ))
    records = []
    for label, representative in enumerate(representatives):
        check()
        t, c, rank = (representative[key] for key in ('tetrahedron', 'column', 'rank'))
        row = rows[t]
        chain, arms, quad, typ = layout[t]
        if c < 4:
            a, b = c, next(v for v in range(4) if v != c)
            edge_rank = rank
            minus = arms[c] + rank
            plus = (minus + 1 if rank + 1 < row[c] else
                    chain + (quad if typ is not None and c not in (0, typ + 1) else 0))
        else:
            a, b = 0, next(v for v in range(4) if v not in (0, c - 3))
            edge_rank = row[a] + rank
            minus, plus = chain + rank, chain + rank + 1
        local = _edge(t, a, b)
        root = prepared['edge_roots'][local]
        backwards = prepared['edge_orientations'][local] ^ int(a > b)
        point = offsets[root] + (analysed['weights'][root] - 1 - edge_rank
                                 if backwards else edge_rank)
        records.append(dict(label=label, surface_point=point,
                            negative_chamber=minus, positive_chamber=plus))
    return total, size, records


def _graph(histogram, count, check):
    """Decode the exact scalar side census with stable chamber labels."""
    if count == 0:
        return dict(vertices=1, edges=[], chamber_masks=[0], cycle_rank=0)
    masks, used = [], 0
    for record in histogram:
        check()
        weight, multiplicity = record['weight'][0], record['orbits']
        if weight <= 0 or multiplicity != 1 or weight.bit_length() > 2 * count or used & weight:
            raise ArithmeticError('invalid authenticated side partition')
        masks.append(weight)
        used |= weight
    if used != (1 << (2 * count)) - 1:
        raise ArithmeticError('the chamber census lost a side marker')
    masks.sort(key=lambda mask: (mask & -mask).bit_length())
    location = {}
    for vertex, mask in enumerate(masks):
        while mask:
            check()
            bit = mask & -mask
            location[bit.bit_length() - 1] = vertex
            mask -= bit
    edges = [[location[2 * i], location[2 * i + 1]] for i in range(count)]
    parent = list(range(len(masks)))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for a, b in edges:
        check()
        parent[root(a)] = root(b)
    if not masks or len({root(v) for v in parent}) != 1:
        raise ArithmeticError('the chamber graph of a connected source is disconnected')
    return dict(vertices=len(masks), edges=edges, chamber_masks=masks,
                cycle_rank=count - len(masks) + 1)


def normal_chamber_graph(triangulation, coordinates, representatives=None, *,
                         max_cycles=None, record_certificate=False, check=lambda: None):
    """Export the oriented graph dual to all components of a normal surface.

    Representatives are explicit ``{tetrahedron, column, rank}`` records,
    indexed from zero.  A missing list tries the first disc; this succeeds
    only for a connected surface (or the empty surface).  Labels must be
    exhaustive and distinct, and every component must be two-sided.  Failure
    of these conditions or of an orbit allowance returns INCONCLUSIVE.

    The two endpoints of edge i are the chambers on the locally chosen
    negative and positive sides of representative i.  They determine a
    coorientation because the entire component has been proved two-sided.
    Any subset J is simultaneously nonseparating precisely when deleting
    the graph edges J leaves a connected graph.  No geometric dual routes,
    edit-persistence proof, hierarchy step or knot verdict are supplied.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    chosen = _representatives(analysed['rows'], representatives, check)
    points, chambers, marks = _markers(prepared, analysed, chosen, check)
    count = len(chosen)
    result = dict(status='INCONCLUSIVE', stats=dict(orbit_cycles=0),
                  trust='source-labelled chamber graph; no knot or edit-persistence verdict')
    proofs = {}
    if analysed['normal_disks'] == 0:
        graph = _graph([], 0, check)
    else:
        if count == 0:
            result['reason'] = 'representatives_do_not_label_components'
            return result
        size, pairs = _arc_system(prepared, analysed, check=check)
        if size != points:
            raise ArithmeticError('surface marker namespace disagrees')
        weights = [(m['surface_point'], m['surface_point'] + 1, [1 << i])
                   for i, m in enumerate(marks)]
        labelled = weighted_orbit_histogram(size, pairs, weights, dimension=1,
            max_cycles=max_cycles, record_certificate=record_certificate, check=check)
        result['stats']['surface_labels'] = labelled['stats']
        used = labelled['stats']['orbit_cycles']
        result['stats']['orbit_cycles'] = used
        if labelled['status'] != 'COMPLETE':
            result['reason'] = 'shared_orbit_allowance_exhausted'
            return result
        expected = [dict(weight=[1 << i], orbits=1) for i in range(count)]
        if labelled['histogram'] != expected:
            result['reason'] = 'representatives_do_not_label_components'
            return result
        size, pairs = _arc_system(prepared, analysed, scale=2, check=check)
        doubled = count_orbits(size, pairs, max_cycles=None if max_cycles is None else max_cycles - used,
                               record_certificate=record_certificate, check=check)
        used += doubled.cycles
        result['stats']['orientation_double'] = dict(orbit_cycles=doubled.cycles, **doubled.stats)
        result['stats']['orbit_cycles'] = used
        if not doubled.complete:
            result['reason'] = 'shared_orbit_allowance_exhausted'
            return result
        if doubled.orbits != 2 * count:
            result['reason'] = 'one_sided_surface_component'
            return result
        size, pairs = _chamber_system(prepared, analysed['rows'], check)
        if size != chambers:
            raise ArithmeticError('chamber marker namespace disagrees')
        weights = []
        for i, marker in enumerate(marks):
            check()
            for side, key in enumerate(('negative_chamber', 'positive_chamber')):
                point = marker[key]
                weights.append((point, point + 1, [1 << (2 * i + side)]))
        sides = weighted_orbit_histogram(size, pairs, weights, dimension=1,
            max_cycles=None if max_cycles is None else max_cycles - used,
            record_certificate=record_certificate, check=check)
        result['stats']['chamber_sides'] = sides['stats']
        used += sides['stats']['orbit_cycles']
        result['stats']['orbit_cycles'] = used
        if sides['status'] != 'COMPLETE':
            result['reason'] = 'shared_orbit_allowance_exhausted'
            return result
        graph = _graph(sides['histogram'], count, check)
        if record_certificate:
            proofs = dict(surface_labels=labelled['certificate'],
                          orientation_double=doubled.certificate, chamber_sides=sides['certificate'])
    result.update(status='COMPLETE', graph=graph, representatives=chosen, markers=marks,
                  surface_components=count, normal_disks=analysed['normal_disks'],
                  surface_points=points, chamber_points=chambers)
    if record_certificate:
        result['certificate'] = dict(schema='normal-chamber-graph-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            representatives=chosen, markers=marks, graph=graph, proofs=proofs)
    check()
    return result
