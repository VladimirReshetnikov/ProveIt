"""Exact quadratic-integer Potts obstruction for any fixed q >= 5.

Compute in Z[x]/(x^2-(q-2)x+1), storing a+b*x as the integer pair (a,b).
The spin edge weight is 1 for different colors and -x**(-e) for equal
colors, where e is the omitted smoothing exponent.  No floating point,
prime choice, or division is used.  Agreement still means INCONCLUSIVE.
The default is q=6; q=5 misses every odd member of an infinite weaving
knot family, including closure((sigma1 sigma2^-1)^5).
"""
from __future__ import annotations

from .filters import FilterLimit
from .ordering import best_scan_order, validate_order
from .potts import (_budget, _canonical, _checkerboard, _extensions,
                    _schedule, _tait_from_faces)


class PottsLimit(FilterLimit):
    """Local exhaustion with work counters, never a partially computed value."""
    def __init__(self, message, *, transitions=0, peak_states=0, completed_crossings=0):
        super().__init__(message)
        self.transitions = transitions
        self.peak_states = peak_states
        self.completed_crossings = completed_crossings


def ring_label(colors):
    """Keep huge color counts out of decimal formatting and its global limit."""
    return (f"Z[x]/(x^2-{colors - 2}*x+1)" if colors.bit_length() <= 256
            else "Z[x]/(x^2-(q-2)*x+1)")


def multiply(left, right, colors=6):
    """Exact quadratic-ring multiplication; x^2=(colors-2)*x-1."""
    a, b = left
    c, d = right
    bd = b * d
    return a * c - bd, a * d + b * c + (colors - 2) * bd


def power(value, exponent, colors=6):
    """Nonnegative integral powers in the quadratic ring."""
    if type(exponent) is not int or exponent < 0:
        raise ValueError("exponent must be a nonnegative integer")
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = multiply(result, value, colors)
        exponent >>= 1
        if exponent:
            value = multiply(value, value, colors)
    return result


def x_power(exponent, colors=6):
    if type(exponent) is not int:
        raise ValueError("exponent must be an integer")
    return power((0, 1) if exponent >= 0 else (colors - 2, -1), abs(exponent), colors)


def equal_spin(value, omitted_exponent, colors=6):
    """Multiply by -x**(-omitted_exponent) with additions only."""
    a, b = value
    if omitted_exponent == 1:
        return -(colors - 2) * a - b, a
    if omitted_exponent == -1:
        return b, -a - (colors - 2) * b
    raise ValueError("omitted smoothing exponent must be +1 or -1")


def potts_exact(diagram, *, colors=6, max_states=4096, max_transitions=200_000,
                order=None, check=lambda: None, statistics=None, shade=None,
                _stage_check=None):
    """Return the exact partition function and its unknot comparison.

    For a nonempty classical knot diagram let v be the Tait vertex count,
    s the sum of omitted smoothing exponents, and w the writhe. Then

      E = s - 3*w + 2*(v+1) is a multiple of 4,
      V(A^-4) = (-1)**(w+v+1) * x**(E/4) * Z / (x+1)**(v+1).

    We compare Z with (-1)**(w+v+1)*x**(-E/4)*(x+1)**(v+1).
    The quadratic polynomial is irreducible over Q for every integer q>=5,
    so pair inequality certifies exact inequality. Intermediate coefficients
    have O(n log q) bits. The number of colors is a parameter, not a field.
    """
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if type(colors) is not int or colors < 5:
        raise ValueError("colors must be an integer at least 5")
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError("shade must be 0, 1, or None")
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise PottsLimit("exact Potts filter budget is zero")
    if n == 0:
        result = dict(q=colors, ring=ring_label(colors), writhe=0,
                      partition_function=[colors, 0], unknot_partition=[colors, 0],
                      differs=False, tait_vertices=1, shade=0 if shade is None else shade,
                      peak_states=1, transitions=0, max_spin_frontier=0,
                      max_boundary=0, crossing_count=0,
                      max_coefficient_bits=colors.bit_length(),
                      normalization_exponent=None, omitted_exponent=None)
        if statistics is not None:
            statistics.update(result)
        return result
    if order is None:
        order = best_scan_order(diagram.pd, tries=min(n, 12), check=check)
    dart_face, face_colors = _checkerboard(diagram, check)
    selected = None
    for candidate in ((0, 1) if shade is None else (shade,)):
        check()
        vertices, edges = _tait_from_faces(n, dart_face, face_colors, candidate)
        first, last, profile = _schedule(vertices, edges, order)
        choice = (profile, candidate, vertices, edges, first, last)
        if selected is None or choice[:2] < selected[:2]:
            selected = choice
    profile, shade, vertices, edges, first, last = selected
    states, active = {(): (1, 0)}, []
    peak, transitions, max_boundary, coefficient_bits = 1, 0, 0, 1
    boundary = set()
    for position, index in enumerate(order):
        check()
        u, v, exponent = edges[index]
        new_vertices = sorted(vertex for vertex in {u, v} if first[vertex] == position)
        extended = active + new_vertices
        iu, iv = extended.index(u), extended.index(v)
        keep = tuple(i for i, vertex in enumerate(extended) if last[vertex] > position)
        following = {}
        for state, coefficient in states.items():
            for values, multiplicity, _ in _extensions(state, len(new_vertices), colors):
                if max_transitions is not None and transitions >= max_transitions:
                    raise PottsLimit("exact Potts transition budget exhausted", transitions=transitions,
                                     peak_states=peak, completed_crossings=position)
                transitions += 1
                if not transitions & 1023:
                    check()
                a, b = (equal_spin(coefficient, exponent, colors)
                        if values[iu] == values[iv] else coefficient)
                target = _canonical(values[i] for i in keep)
                old_a, old_b = following.get(target, (0, 0))
                value = old_a + multiplicity * a, old_b + multiplicity * b
                if value != (0, 0):
                    following[target] = value
                    peak = max(peak, len(following))
                    coefficient_bits = max(coefficient_bits, abs(value[0]).bit_length(),
                                           abs(value[1]).bit_length())
                else:
                    following.pop(target, None)
                if max_states is not None and len(following) > max_states:
                    raise PottsLimit("exact Potts frontier budget exhausted", transitions=transitions,
                                     peak_states=peak, completed_crossings=position)
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
        if _stage_check is not None and position+1 < n:
            _stage_check(position+1, transitions, peak)
    if active or boundary or any(states):
        raise ArithmeticError("exact Potts scan ended with an open frontier")
    check()
    partition = states.get((), (0, 0))
    omitted_exponent = sum(edge[2] for edge in edges)
    writhe = diagram.writhe()
    exponent = omitted_exponent - 3 * writhe + 2 * (vertices + 1)
    if exponent % 4:
        raise ArithmeticError("normalization requires an odd-component classical link")
    exponent //= 4
    expected = multiply(x_power(-exponent, colors),
                        power((1, 1), vertices + 1, colors), colors)
    if (writhe + vertices + 1) % 2:
        expected = -expected[0], -expected[1]
    check()
    result = dict(q=colors, ring=ring_label(colors), writhe=writhe,
                  partition_function=list(partition), unknot_partition=list(expected),
                  differs=partition != expected, tait_vertices=vertices, shade=shade,
                  peak_states=peak, transitions=transitions,
                  max_spin_frontier=profile[0], max_boundary=max_boundary,
                  crossing_count=n, max_coefficient_bits=coefficient_bits,
                  normalization_exponent=exponent, omitted_exponent=omitted_exponent)
    if statistics is not None:
        statistics.update(result)
    return result


def witness_from_exact(result, *, kind="potts-jones-exact-differs-from-unknot"):
    """JSON-safe exact witness, or None; raw evaluators retain integer pairs.

    Signed hexadecimal strings avoid Python's decimal integer digit limit
    for long bounded-width inputs without altering a process-global setting.
    The equality test uses the actual pairs, not a supplied truthy flag.
    """
    partition = result["partition_function"]
    expected = result["unknot_partition"]
    if partition == expected:
        return None
    witness = dict(kind=kind, **result)
    witness["differs"] = True
    if 'q' in witness and witness['q'].bit_length() > 256:
        witness['q_hex'] = hex(witness.pop('q'))
    for name in ("partition_function", "unknot_partition"):
        witness[name + "_hex"] = [hex(value) for value in witness.pop(name)]
    return witness


def potts_exact_obstruction(diagram, **options):
    """An exact nontrivial-Jones-value witness, or None (inconclusive)."""
    return witness_from_exact(potts_exact(diagram, **options))
