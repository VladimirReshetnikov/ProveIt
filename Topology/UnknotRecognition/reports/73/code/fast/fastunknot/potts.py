"""Exact five-state Potts specialization of the Jones obstruction.

The signed checkerboard graph turns the bracket into a Potts partition
function at q=5.  At any supplied crossing order its active black regions
number at most half the diagram's cut edges.  A state records the equality
pattern of their spins, with at most five classes.  Simultaneous permutation
of the five spin names is quotiented exactly; coefficients are AGGREGATED
over all labeled assignments in a class, not per-assignment coefficients.

This is an optional one-sided filter.  Equality with the unknot value is
inconclusive, and FilterLimit is a resource outcome, never a knot verdict.
The polynomial specialization differs from the original generic Jones
evaluation, so neither filter subsumes the other.
"""
from __future__ import annotations

from .filters import FilterLimit, PRIME
from .ordering import best_scan_order, validate_order


COLORS = 5
# p = 2^61-1 is 3 modulo 4 and 1 modulo 5.  x=(3+sqrt(5))/2 is a
# square, and the squares have odd order 2^60-1; 4^(-1) in that
# subgroup is 2^58.  Thus A^4=x and (-A^2-A^(-2))^2=5.
ROOT_FIVE = pow(5, (PRIME + 1) // 4, PRIME)
POTTS_X = (3 + ROOT_FIVE) * ((PRIME + 1) // 2) % PRIME
POTTS_A = pow(POTTS_X, 1 << 58, PRIME)
_INVERSE_A = pow(POTTS_A, -1, PRIME)
POTTS_DELTA = (-POTTS_A * POTTS_A - _INVERSE_A * _INVERSE_A) % PRIME
if (ROOT_FIVE * ROOT_FIVE % PRIME != 5 or pow(POTTS_A, 4, PRIME) != POTTS_X
        or POTTS_DELTA * POTTS_DELTA % PRIME != COLORS):
    raise ArithmeticError("invalid five-state Potts specialization")


def _budget(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name + " must be a nonnegative integer or None")


def _checkerboard(diagram, check):
    """Face IDs of outgoing darts and the two colors of the dual graph."""
    faces = diagram.faces()
    alpha = diagram.alpha()
    dart_face = [0] * len(alpha)
    for number, face in enumerate(faces):
        for dart in face:
            dart_face[dart] = number
    colors = [-1] * len(faces)
    if not faces:
        return dart_face, colors
    colors[0] = 0
    queue = [0]
    while queue:
        face = queue.pop()
        check()
        opposite = 1 - colors[face]
        for dart in faces[face]:
            other = dart_face[alpha[dart]]
            if colors[other] == -1:
                colors[other] = opposite
                queue.append(other)
            elif colors[other] != opposite:
                raise ValueError("diagram faces are not checkerboard colorable")
    if any(color == -1 for color in colors):
        raise ValueError("the projection must be connected")
    return dart_face, colors


def _tait_from_faces(n, dart_face, colors, shade):
    names = {face: i for i, face in enumerate(
        face for face, color in enumerate(colors) if color == shade)}
    edges = []
    for crossing in range(n):
        base = 4 * crossing
        # The face walk is sigma o alpha.  Hence corner (j,j+1)
        # is the face of outgoing dart j+1, rather than dart j.
        corners = [dart_face[base + (j + 1) % 4] for j in range(4)]
        if colors[corners[0]] == shade:
            # Smoothing 0 caps both black corners and omits the Tait edge.
            u, v, exponent = corners[0], corners[2], 1
        else:
            # Smoothing 1 caps both black corners and omits the Tait edge.
            u, v, exponent = corners[1], corners[3], -1
        edges.append((names[u], names[v], exponent))
    return len(names), tuple(edges)


def tait_graph(diagram, *, shade=0, check=lambda: None):
    """Return (vertex_count, edges) of the signed Tait multigraph.

    Edge i is (u,v,e), where omitting that edge uses smoothing exponent
    e in {+1,-1}.  Loops and parallel edges are retained.  ``diagram``
    must be a validated classical one-component Diagram, as for the
    original scanner APIs.  The crossing-free input has one black vertex.
    """
    if type(shade) is not int or shade not in (0, 1):
        raise ValueError("shade must be 0 or 1")
    check()
    if not diagram.pd:
        return 1, ()
    dart_face, colors = _checkerboard(diagram, check)
    return _tait_from_faces(diagram.crossings, dart_face, colors, shade)


def _schedule(vertices, edges, order):
    first, last = [len(order)] * vertices, [-1] * vertices
    for position, index in enumerate(order):
        u, v, _ = edges[index]
        for vertex in (u,) if u == v else (u, v):
            if first[vertex] == len(order):
                first[vertex] = position
            last[vertex] = position
    changes = [0] * len(order)
    for vertex in range(vertices):
        if last[vertex] < 0:
            raise ArithmeticError("an isolated Tait vertex was not accounted for")
        changes[first[vertex]] += 1
        changes[last[vertex]] -= 1
    active = peak = total = 0
    for change in changes:
        active += change
        peak = max(peak, active)
        total += active
    return first, last, (peak, total)


def _canonical(values):
    names = {}
    result = []
    for value in values:
        if value not in names:
            names[value] = len(names)
        result.append(names[value])
    return tuple(result)


def _extensions(state, introduced, colors=COLORS):
    """(extended equality pattern, multiplicity of new labeled choices)."""
    patterns = [(state, 1, max(state, default=-1) + 1)]
    for _ in range(introduced):
        following = []
        for values, multiplicity, used in patterns:
            for color in range(used):
                following.append((values + (color,), multiplicity, used))
            if used < colors:
                following.append((values + (used,), multiplicity * (colors - used),
                                  used + 1))
        patterns = following
    return patterns


def potts_bracket(diagram, *, max_states=4096, max_transitions=200_000,
                  order=None, check=lambda: None, statistics=None, shade=None):
    """Compute an exact modular bracket evaluation and its work counters.

    shade=None selects between the two checkerboard graphs by the
    (maximum, total) active-vertex profile in this SAME crossing order.
    Passing shade=0 or shade=1 forces a graph for independent checks.
    Only the current frontier is stored; preparation uses O(n) space.
    The optional ``statistics`` dictionary is updated on successful return.
    A zero state or transition budget skips every nonempty diagram.
    """
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError("shade must be 0, 1, or None")
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise FilterLimit("Potts filter budget is zero")
    if n == 0:
        result = dict(prime=PRIME, q=COLORS, A=POTTS_A, x=POTTS_X,
                      delta=POTTS_DELTA, writhe=0, bracket=POTTS_DELTA,
                      unknot_bracket=POTTS_DELTA, partition_function=COLORS,
                      tait_vertices=1, shade=0 if shade is None else shade,
                      peak_states=1, transitions=0, max_spin_frontier=0,
                      max_boundary=0, crossing_count=0)
        if statistics is not None:
            statistics.update(result)
        return result
    if order is None:
        order = best_scan_order(diagram.pd, tries=min(n, 12), check=check)
    check()
    dart_face, colors = _checkerboard(diagram, check)
    choices = (0, 1) if shade is None else (shade,)
    selected = None
    for candidate in choices:
        vertices, edges = _tait_from_faces(n, dart_face, colors, candidate)
        first, last, profile = _schedule(vertices, edges, order)
        choice = (profile, candidate, vertices, edges, first, last)
        if selected is None or choice[:2] < selected[:2]:
            selected = choice
    profile, shade, vertices, edges, first, last = selected
    check()

    states, active = {(): 1}, []
    peak, transitions, max_boundary = 1, 0, 0
    boundary = set()
    # For omitted smoothing exponent e, v_e=delta*A^(-2e).
    # Their equal-spin factors are 1+v_e=-x^(-e).
    equal_weights = {1: (-pow(POTTS_X, -1, PRIME)) % PRIME,
                     -1: (-POTTS_X) % PRIME}
    for position, index in enumerate(order):
        check()
        u, v, exponent = edges[index]
        new_vertices = sorted(vertex for vertex in {u, v} if first[vertex] == position)
        extended = active + new_vertices
        iu, iv = extended.index(u), extended.index(v)
        keep = tuple(i for i, vertex in enumerate(extended) if last[vertex] > position)
        following = {}
        equal = equal_weights[exponent]
        introduced = len(new_vertices)
        for state, coefficient in states.items():
            for values, multiplicity, _ in _extensions(state, introduced):
                if max_transitions is not None and transitions >= max_transitions:
                    raise FilterLimit("Potts transition budget exhausted")
                transitions += 1
                if not transitions & 1023:
                    check()
                weight = equal if values[iu] == values[iv] else 1
                target = _canonical(values[i] for i in keep)
                value = (following.get(target, 0) + coefficient * multiplicity * weight) % PRIME
                if value:
                    following[target] = value
                    peak = max(peak, len(following))
                else:
                    following.pop(target, None)
                if max_states is not None and len(following) > max_states:
                    raise FilterLimit("Potts frontier budget exhausted")
        active = [extended[i] for i in keep]
        states = following
        peak = max(peak, len(states))
        for label in diagram.pd[index]:
            if label in boundary:
                boundary.remove(label)
            else:
                boundary.add(label)
        max_boundary = max(max_boundary, len(boundary))
        if 2 * len(active) > len(boundary):
            raise ArithmeticError("checkerboard frontier violates the cut-edge bound")
    if active or boundary or any(states):
        raise ArithmeticError("Potts scan ended with an open frontier")
    check()
    partition = states.get((), 0)
    omitted_exponent = sum(edge[2] for edge in edges)
    prefactor = (pow(POTTS_A, omitted_exponent, PRIME)
                 * pow(POTTS_DELTA, -vertices, PRIME)) % PRIME
    bracket = partition * prefactor % PRIME
    writhe = diagram.writhe()
    expected = POTTS_DELTA * pow((-pow(POTTS_A, 3, PRIME)) % PRIME,
                                writhe % (PRIME - 1), PRIME) % PRIME
    result = dict(prime=PRIME, q=COLORS, A=POTTS_A, x=POTTS_X,
                  delta=POTTS_DELTA, writhe=writhe, bracket=bracket,
                  unknot_bracket=expected, partition_function=partition,
                  tait_vertices=vertices, shade=shade, peak_states=peak,
                  transitions=transitions, max_spin_frontier=profile[0],
                  max_boundary=max_boundary, crossing_count=n)
    if statistics is not None:
        statistics.update(result)
    return result


def potts_obstruction(diagram, *, max_states=4096, max_transitions=200_000,
                      order=None, check=lambda: None, statistics=None, shade=None):
    """Return an exact knottedness witness or None; never certify an unknot."""
    result = potts_bracket(diagram, max_states=max_states, max_transitions=max_transitions,
                           order=order, check=check, statistics=statistics, shade=shade)
    if result["bracket"] == result["unknot_bracket"]:
        return None
    return dict(kind="potts-jones-differs-from-unknot", **result)
