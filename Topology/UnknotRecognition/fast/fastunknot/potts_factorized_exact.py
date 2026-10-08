"""Exact quadratic-integer Potts tensors with processed-component factoring.

This module uses the scalar-ring helpers of potts_exact and the color-orbit
alignment enumeration of potts_factorized.  Its transfer loop is separate
from both independent scalar implementations.  Orbit aggregates are divided
by their integer orbit sizes with an explicit remainder check.
"""
from __future__ import annotations

from .filters import FilterLimit
from .ordering import best_scan_order, validate_order
from .potts import _budget, _canonical, _checkerboard, _schedule, _tait_from_faces
from .potts_exact import equal_spin, multiply, potts_exact, power, x_power
from .potts_factorized import relative_alignments


def factorized_exact_partition(vertices, edges, order, *, colors=6,
                                max_states=4096, max_transitions=200_000,
                                check=lambda: None):
    """Exact signed-graph partition function in Z[x]/(x²-(q-2)x+1).

    Edge labels ±1 are omitted smoothing exponents.  Equal-spin weights
    are -x^(-exponent).  q=colors is an integer at least five.
    Limits have the same represented-key and orbit-update meanings as
    factorized_partition; no finite-prime arithmetic is used here.
    """
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if type(colors) is not int or colors < 5:
        raise ValueError("colors must be an integer at least five")
    if type(vertices) is not int or vertices < 0:
        raise ValueError("vertices must be a nonnegative integer")
    edges = tuple(edges)
    order = validate_order(len(edges), order)
    for u, v, exponent in edges:
        if (type(u) is not int or type(v) is not int or not 0 <= u < vertices
                or not 0 <= v < vertices or type(exponent) is not int
                or exponent not in (-1, 1)):
            raise ValueError("invalid signed graph edge")
    if edges and (max_states == 0 or max_transitions == 0):
        raise FilterLimit("factorized exact Potts filter budget is zero")
    check()
    first, last = [len(edges)] * vertices, [-1] * vertices
    for position, index in enumerate(order):
        u, v, _ = edges[index]
        for vertex in (u,) if u == v else (u, v):
            first[vertex] = min(first[vertex], position)
            last[vertex] = position
    scalar = colors ** sum(position == -1 for position in last), 0
    falling = [1]
    for k in range(1, min(colors, vertices) + 1):
        falling.append(falling[-1] * (colors - k + 1))
    parent = [-1] * vertices
    components = {}
    stored = transitions = merges = 0
    peak = peak_component = 1
    max_components = max_frontier = max_component_frontier = frontier = 0
    coefficient_bits = max(1, scalar[0].bit_length())

    def find(vertex):
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def normalize(state, value):
        used = max(state) + 1
        size = falling[used]
        if value[0] % size or value[1] % size:
            raise ArithmeticError("a component aggregate is not divisible by its color orbit")
        return state, (value[0] // size, value[1] // size), used

    def update(row, target, value, unaffected):
        nonlocal peak, peak_component, transitions, coefficient_bits
        if max_transitions is not None and transitions >= max_transitions:
            raise FilterLimit("factorized exact Potts transition budget exhausted")
        transitions += 1
        if not transitions & 1023:
            check()
        old = row.get(target, (0, 0))
        value = old[0] + value[0], old[1] + value[1]
        if value != (0, 0):
            row[target] = value
            coefficient_bits = max(coefficient_bits, abs(value[0]).bit_length(),
                                   abs(value[1]).bit_length())
        else:
            row.pop(target, None)
        represented = unaffected + len(row)
        peak = max(peak, represented)
        peak_component = max(peak_component, len(row))
        if max_states is not None and represented > max_states:
            raise FilterLimit("factorized exact Potts frontier budget exhausted")

    for position, index in enumerate(order):
        check()
        u, v, exponent = edges[index]
        for vertex in sorted({u, v}):
            if first[vertex] == position:
                parent[vertex] = vertex
                components[vertex] = ([vertex], {(0,): (colors, 0)})
                stored += 1
                frontier += 1
        peak = max(peak, stored)
        max_components = max(max_components, len(components))
        if max_states is not None and stored > max_states:
            raise FilterLimit("factorized exact Potts frontier budget exhausted")
        left_root, right_root = find(u), find(v)
        left_active, left_states = components[left_root]
        row = {}
        if left_root == right_root:
            active = left_active
            iu, iv = active.index(u), active.index(v)
            keep = tuple(i for i, vertex in enumerate(active) if last[vertex] > position)
            unaffected = stored - len(left_states)
            for state, coefficient in left_states.items():
                target = _canonical(state[i] for i in keep)
                value = equal_spin(coefficient, exponent, colors) if state[iu] == state[iv] else coefficient
                update(row, target, value, unaffected)
        else:
            merges += 1
            right_active, right_states = components[right_root]
            active = left_active + right_active
            iu, iv = left_active.index(u), right_active.index(v)
            keep = tuple(i for i, vertex in enumerate(active) if last[vertex] > position)
            unaffected = stored - len(left_states) - len(right_states)
            normalized_left = [normalize(state, value) for state, value in left_states.items()]
            normalized_right = [normalize(state, value) for state, value in right_states.items()]
            for a, ca, ka in normalized_left:
                for b, cb, kb in normalized_right:
                    coefficient = multiply(ca, cb, colors)
                    for alignment, used in relative_alignments(ka, kb, colors):
                        combined = a + tuple(alignment[color] for color in b)
                        target = _canonical(combined[i] for i in keep)
                        value = (equal_spin(coefficient, exponent, colors)
                                 if a[iu] == alignment[b[iv]] else coefficient)
                        size = falling[used]
                        update(row, target, (size * value[0], size * value[1]), unaffected)
            del components[right_root]
            parent[right_root] = left_root
        remaining = [active[i] for i in keep]
        if remaining:
            components[left_root] = (remaining, row)
            stored = unaffected + len(row)
        else:
            scalar = multiply(scalar, row.get((), (0, 0)), colors)
            coefficient_bits = max(coefficient_bits, abs(scalar[0]).bit_length(),
                                   abs(scalar[1]).bit_length())
            del components[left_root]
            stored = unaffected
        frontier -= len(active) - len(remaining)
        max_frontier = max(max_frontier, frontier)
        max_component_frontier = max(max_component_frontier, len(remaining))
    if components:
        raise ArithmeticError("factorized exact Potts scan ended with active components")
    check()
    return dict(partition_function=list(scalar), peak_states=peak,
                peak_component_states=peak_component, transitions=transitions,
                tensor_merges=merges, max_active_components=max_components,
                max_spin_frontier=max_frontier,
                max_component_frontier=max_component_frontier,
                max_coefficient_bits=coefficient_bits)


def factorized_potts_exact(diagram, *, colors=6, max_states=4096,
                            max_transitions=200_000, order=None,
                            check=lambda: None, statistics=None, shade=None):
    """Exact Jones specialization with independent processed-component tensors."""
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if type(colors) is not int or colors < 5:
        raise ValueError("colors must be an integer at least five")
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError("shade must be 0, 1, or None")
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n == 0:
        result = potts_exact(diagram, colors=colors, max_states=max_states,
                             max_transitions=max_transitions, order=order, check=check, shade=shade)
        result.update(peak_component_states=1, tensor_merges=0,
                      max_active_components=0, max_component_frontier=0)
        if statistics is not None:
            statistics.update(result)
        return result
    if max_states == 0 or max_transitions == 0:
        raise FilterLimit("factorized exact Potts filter budget is zero")
    check()
    if order is None:
        order = best_scan_order(diagram.pd, tries=min(n, 12), check=check)
    dart_face, face_colors = _checkerboard(diagram, check)
    selected = None
    for candidate in ((0, 1) if shade is None else (shade,)):
        vertices, edges = _tait_from_faces(n, dart_face, face_colors, candidate)
        _, _, profile = _schedule(vertices, edges, order)
        choice = (profile, candidate, vertices, edges)
        if selected is None or choice[:2] < selected[:2]:
            selected = choice
    profile, shade, vertices, edges = selected
    result = factorized_exact_partition(vertices, edges, order, colors=colors,
                                         max_states=max_states, max_transitions=max_transitions,
                                         check=check)
    boundary = set()
    max_boundary = 0
    for index in order:
        for label in diagram.pd[index]:
            if label in boundary:
                boundary.remove(label)
            else:
                boundary.add(label)
        max_boundary = max(max_boundary, len(boundary))
    omitted_exponent = sum(edge[2] for edge in edges)
    writhe = diagram.writhe()
    exponent = omitted_exponent - 3 * writhe + 2 * (vertices + 1)
    if exponent % 4:
        raise ArithmeticError("normalization requires an odd-component classical link")
    exponent //= 4
    expected = multiply(x_power(-exponent, colors), power((1, 1), vertices + 1, colors), colors)
    if (writhe + vertices + 1) % 2:
        expected = -expected[0], -expected[1]
    result.update(q=colors, ring=f"Z[x]/(x^2-{colors - 2}*x+1)", writhe=writhe,
                  unknot_partition=list(expected), differs=result["partition_function"] != list(expected),
                  tait_vertices=vertices, shade=shade, max_boundary=max_boundary,
                  crossing_count=n, normalization_exponent=exponent,
                  omitted_exponent=omitted_exponent)
    if result["max_spin_frontier"] != profile[0]:
        raise ArithmeticError("factorized frontier differs from the graph schedule")
    check()
    if statistics is not None:
        statistics.update(result)
    return result


def factorized_potts_exact_obstruction(diagram, **options):
    """A one-sided witness, with no finite-field collisions or unknot assertion."""
    from .potts_exact import witness_from_exact
    result = factorized_potts_exact(diagram, **options)
    return witness_from_exact(result, kind="factorized-potts-jones-exact-differs-from-unknot")
