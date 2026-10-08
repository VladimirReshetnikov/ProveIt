"""Potts spin tensors factored over components of the processed Tait graph.

Independent processed components have independent spin-name symmetries.
Keeping them separate avoids storing their currently irrelevant relative
color equalities.  When an edge joins components, exact relative color
alignments restore those equalities.  This is an optional modular backend;
the ordinary one-tensor Potts implementation remains an independent oracle.
"""
from __future__ import annotations

from .filters import FilterLimit, PRIME
from .ordering import best_scan_order, validate_order
from .potts import (COLORS, POTTS_A, POTTS_DELTA, POTTS_X, _budget,
                    _canonical, _checkerboard, _schedule, _tait_from_faces,
                    potts_bracket)


_ALIGNMENTS = {}


def relative_alignments(left_colors, right_colors, colors=COLORS):
    """Yield (right-label map, total used colors), without duplicate orbits.

    A right label is identified with one unused left label or becomes the
    next fresh label.  This enumerates partial bijections of color classes.
    At q=5 there are at most 120, and at q=6 at most 720, alignments per
    pair of states.  Larger q is supported by the uncached lazy generator.
    """
    if (type(colors) is not int or colors < 1 or type(left_colors) is not int
            or type(right_colors) is not int
            or not 0 <= left_colors <= colors or not 0 <= right_colors <= colors):
        raise ValueError("invalid color-class counts")
    key = (left_colors, right_colors, colors)
    cached = _ALIGNMENTS.get(key)
    if cached is not None:
        yield from cached
        return

    def generate(prefix, used_left, fresh):
        if len(prefix) == right_colors:
            yield prefix, left_colors + fresh
            return
        for value in range(left_colors):
            if not used_left >> value & 1:
                yield from generate(prefix + (value,), used_left | (1 << value), fresh)
        if left_colors + fresh < colors:
            yield from generate(prefix + (left_colors + fresh,), used_left, fresh + 1)

    if colors <= 6:
        cached = tuple(generate((), 0, 0))
        _ALIGNMENTS[key] = cached
        yield from cached
    else:
        yield from generate((), 0, 0)


def factorized_partition(vertices, edges, order, *, colors=COLORS,
                          equal_weights=None, max_states=4096,
                          max_transitions=200_000, check=lambda: None):
    """Partition function of a signed graph, with component spin tensors.

    Coefficients are reduced modulo PRIME.  ``colors`` may be any positive
    integer below PRIME; the kernel's asymptotic claim fixes that integer.
    ``equal_weights[e]`` is the multiplier for equal endpoint spins at an
    edge with label e; unequal spins have multiplier one.  Default weights
    implement the same q=5 Jones specialization as potts_bracket.

    A state limit bounds the SUM of represented table keys, including
    independent components.  Inputs to a merge remain allocated while its
    replacement is constructed, so this is not a process-memory ceiling.
    Transition work counts resulting relative-color orbits, or one update
    per state for an edge inside one component.  Isolated vertices and
    closed components contribute scalar factors.
    """
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if type(colors) is not int or not 1 <= colors < PRIME:
        raise ValueError("colors must be a positive integer below PRIME")
    if type(vertices) is not int or vertices < 0:
        raise ValueError("vertices must be a nonnegative integer")
    edges = tuple(edges)
    order = validate_order(len(edges), order)
    if equal_weights is None:
        if colors != COLORS:
            raise ValueError("nondefault colors require explicit equal_weights")
        equal_weights = {1: -pow(POTTS_X, -1, PRIME), -1: -POTTS_X}
    for u, v, exponent in edges:
        if (type(u) is not int or type(v) is not int or not 0 <= u < vertices
                or not 0 <= v < vertices or exponent not in equal_weights
                or type(equal_weights[exponent]) is not int):
            raise ValueError("invalid signed graph edge")
    if edges and (max_states == 0 or max_transitions == 0):
        raise FilterLimit("factorized Potts filter budget is zero")
    check()
    first, last = [len(edges)] * vertices, [-1] * vertices
    for position, index in enumerate(order):
        u, v, _ = edges[index]
        for vertex in (u,) if u == v else (u, v):
            first[vertex] = min(first[vertex], position)
            last[vertex] = position
    scalar = pow(colors, sum(position == -1 for position in last), PRIME)
    falling = [1]
    for k in range(1, min(colors, vertices) + 1):
        falling.append(falling[-1] * (colors - k + 1) % PRIME)
    inverse_falling = [pow(value, -1, PRIME) for value in falling]
    parent = [-1] * vertices
    components = {}
    stored = transitions = merges = 0
    peak = peak_component = 1
    max_components = max_frontier = max_component_frontier = frontier = 0

    def find(vertex):
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def update(row, target, value, unaffected):
        nonlocal peak, peak_component, transitions
        if max_transitions is not None and transitions >= max_transitions:
            raise FilterLimit("factorized Potts transition budget exhausted")
        transitions += 1
        if not transitions & 1023:
            check()
        value = (row.get(target, 0) + value) % PRIME
        if value:
            row[target] = value
        else:
            row.pop(target, None)
        represented = unaffected + len(row)
        peak = max(peak, represented)
        peak_component = max(peak_component, len(row))
        if max_states is not None and represented > max_states:
            raise FilterLimit("factorized Potts frontier budget exhausted")

    for position, index in enumerate(order):
        check()
        u, v, exponent = edges[index]
        for vertex in sorted({u, v}):
            if first[vertex] == position:
                parent[vertex] = vertex
                components[vertex] = ([vertex], {(0,): colors})
                stored += 1
                frontier += 1
        peak = max(peak, stored)
        max_components = max(max_components, len(components))
        if max_states is not None and stored > max_states:
            raise FilterLimit("factorized Potts frontier budget exhausted")
        left_root, right_root = find(u), find(v)
        left_active, left_states = components[left_root]
        equal = equal_weights[exponent] % PRIME
        row = {}
        if left_root == right_root:
            active = left_active
            iu, iv = active.index(u), active.index(v)
            keep = tuple(i for i, vertex in enumerate(active) if last[vertex] > position)
            unaffected = stored - len(left_states)
            for state, coefficient in left_states.items():
                target = _canonical(state[i] for i in keep)
                weight = equal if state[iu] == state[iv] else 1
                update(row, target, coefficient * weight, unaffected)
        else:
            merges += 1
            right_active, right_states = components[right_root]
            active = left_active + right_active
            iu, iv = left_active.index(u), right_active.index(v)
            keep = tuple(i for i, vertex in enumerate(active) if last[vertex] > position)
            unaffected = stored - len(left_states) - len(right_states)
            # Divide each aggregate by its orbit size before combining
            # independent label symmetries.  The denominators are units.
            normalized_left = [(state, coefficient * inverse_falling[max(state) + 1] % PRIME,
                                max(state) + 1) for state, coefficient in left_states.items()]
            normalized_right = [(state, coefficient * inverse_falling[max(state) + 1] % PRIME,
                                 max(state) + 1) for state, coefficient in right_states.items()]
            for a, ca, ka in normalized_left:
                for b, cb, kb in normalized_right:
                    coefficient = ca * cb % PRIME
                    for alignment, used in relative_alignments(ka, kb, colors):
                        combined = a + tuple(alignment[color] for color in b)
                        target = _canonical(combined[i] for i in keep)
                        weight = equal if a[iu] == alignment[b[iv]] else 1
                        update(row, target, coefficient * falling[used] * weight, unaffected)
            del components[right_root]
            parent[right_root] = left_root
        remaining = [active[i] for i in keep]
        if remaining:
            components[left_root] = (remaining, row)
            stored = unaffected + len(row)
        else:
            scalar = scalar * row.get((), 0) % PRIME
            del components[left_root]
            stored = unaffected
        frontier -= len(active) - len(remaining)
        max_frontier = max(max_frontier, frontier)
        max_component_frontier = max(max_component_frontier, len(remaining))
    if components:
        raise ArithmeticError("factorized Potts scan ended with active components")
    check()
    return dict(partition_function=scalar, peak_states=peak,
                peak_component_states=peak_component, transitions=transitions,
                tensor_merges=merges, max_active_components=max_components,
                max_spin_frontier=max_frontier,
                max_component_frontier=max_component_frontier)


def factorized_potts_bracket(diagram, *, max_states=4096, max_transitions=200_000,
                             order=None, check=lambda: None, statistics=None, shade=None):
    """Five-state Jones evaluation with processed-component spin factorization."""
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError("shade must be 0, 1, or None")
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n == 0:
        result = potts_bracket(diagram, max_states=max_states, max_transitions=max_transitions,
                               order=order, check=check, shade=shade)
        result.update(peak_component_states=1, tensor_merges=0,
                      max_active_components=0, max_component_frontier=0)
        if statistics is not None:
            statistics.update(result)
        return result
    if max_states == 0 or max_transitions == 0:
        raise FilterLimit("factorized Potts filter budget is zero")
    check()
    if order is None:
        order = best_scan_order(diagram.pd, tries=min(n, 12), check=check)
    dart_face, colors = _checkerboard(diagram, check)
    choices = (0, 1) if shade is None else (shade,)
    selected = None
    for candidate in choices:
        vertices, edges = _tait_from_faces(n, dart_face, colors, candidate)
        first, last, profile = _schedule(vertices, edges, order)
        choice = (profile, candidate, vertices, edges)
        if selected is None or choice[:2] < selected[:2]:
            selected = choice
    profile, shade, vertices, edges = selected
    result = factorized_partition(vertices, edges, order, max_states=max_states,
                                   max_transitions=max_transitions, check=check)
    boundary = set()
    max_boundary = 0
    for index in order:
        for label in diagram.pd[index]:
            if label in boundary:
                boundary.remove(label)
            else:
                boundary.add(label)
        max_boundary = max(max_boundary, len(boundary))
    exponent = sum(edge[2] for edge in edges)
    bracket = (result["partition_function"] * pow(POTTS_A, exponent, PRIME)
               * pow(POTTS_DELTA, -vertices, PRIME)) % PRIME
    writhe = diagram.writhe()
    expected = POTTS_DELTA * pow((-pow(POTTS_A, 3, PRIME)) % PRIME,
                                writhe % (PRIME - 1), PRIME) % PRIME
    result.update(prime=PRIME, q=COLORS, A=POTTS_A, x=POTTS_X, delta=POTTS_DELTA,
                  writhe=writhe, bracket=bracket, unknot_bracket=expected,
                  tait_vertices=vertices, shade=shade, max_boundary=max_boundary,
                  crossing_count=n)
    if result["max_spin_frontier"] != profile[0]:
        raise ArithmeticError("factorized frontier differs from the graph schedule")
    if statistics is not None:
        statistics.update(result)
    return result


def factorized_potts_obstruction(diagram, **options):
    """Exact one-sided witness at the same specialization as potts_obstruction."""
    result = factorized_potts_bracket(diagram, **options)
    if result["bracket"] == result["unknot_bracket"]:
        return None
    return dict(kind="factorized-potts-jones-differs-from-unknot", **result)
