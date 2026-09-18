"""One-sided polynomial-time (or width-bounded) knottedness filters.

Both filters can only answer "KNOTTED" or "inconclusive"; agreement with the
unknot's value never produces an UNKNOT verdict, and exhausting a filter budget
merely skips the filter.  Both were proposed by the acceleration proposals.

* ``alexander_obstruction``: the first Alexander minor evaluated at t = -1 and
  at a generic point of the prime field F_p.  For the unknot the minor is a unit +-t^k of
  Z[t, 1/t] with 0 <= k < n, so an evaluation outside {+-v^k} proves the knot
  nontrivial.  O(n^3) field operations instead of fraction-free elimination
  over Z[t].
* ``jones_obstruction``: the Kauffman bracket at a generic A in F_p, computed by
  scanning the diagram and summing state weights as soon as partial smoothings
  induce the same boundary matching.  Its cost is bounded by the number of
  crossingless matchings of the scan boundary (Catalan(w/2)), with no
  multiplicity factor: unlike the Khovanov scan it really is 2^O(w) poly(n).
  A value different from delta * (-A^3)^writhe proves the knot nontrivial.
"""
from __future__ import annotations

from typing import Callable

from .alexander import alexander_matrix
from .diagram import Diagram
from .geometry import SMOOTHINGS
from .ordering import best_scan_order

PRIME = (1 << 61) - 1      # a Mersenne prime
# Evaluation points.  They are deliberately NOT small integers: 2 has
# multiplicative order 61 modulo 2^61 - 1, so {+-2^k} is a tiny structured set
# and cyclotomic-looking invariants (torus knots) can land in it.  Proposal 03,
# which uses p = 2^31 - 1 and t = 2, misses T(3,61) for exactly this reason:
# Delta(2) = -2^29 mod p.  Generic constants make a false "inconclusive"
# as unlikely as a random collision (about n / 2^60).
ALEXANDER_T = 0x2545F4914F6CDD1D % PRIME
JONES_A = 0x9E3779B97F4A7C15 % PRIME


class FilterLimit(RuntimeError):
    """An optional filter ran out of budget; this proves nothing."""


def _evaluate(poly, value: int, p: int) -> int:
    result = 0
    for c in reversed(poly):
        result = (result * value + c) % p
    return result


def determinant_mod(matrix, p: int = PRIME, reduced: bool = False) -> int:
    """Determinant modulo p.  ``reduced`` promises entries already in [0, p); the matrix is consumed."""
    n = len(matrix)
    a = matrix if reduced else [[x % p for x in row] for row in matrix]
    det = 1
    for k in range(n):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            det = -det
        pivot = a[k][k]
        det = det * pivot % p
        inv = pow(pivot, -1, p)
        row_k = a[k]
        nonzero = [(j, row_k[j]) for j in range(k + 1, n) if row_k[j]]
        for i in range(k + 1, n):
            if a[i][k]:
                factor = a[i][k] * inv % p
                row_i = a[i]
                for j, c in nonzero:
                    row_i[j] = (row_i[j] - factor * c) % p
    return det % p


def alexander_obstruction(diagram: Diagram) -> dict | None:
    """A witness that the Alexander polynomial is not a unit, or None (inconclusive)."""
    n = diagram.crossings
    if n == 0:
        return None
    matrix = alexander_matrix(diagram)
    for value in (-1, ALEXANDER_T):
        # a row has at most three nonzero entries: evaluate those only
        minor = [[_evaluate(x, value, PRIME) if x else 0 for x in row[:-1]] for row in matrix[:-1]]
        det = determinant_mod(minor, reduced=True)
        units, term = set(), 1
        for _ in range(n):
            units.add(term)
            units.add(-term % PRIME)
            term = term * value % PRIME
        if det not in units:
            return {"kind": "alexander-minor-not-a-unit", "prime": PRIME, "t": value, "minor": det}
    return None


def _glue(matching: tuple, slots: tuple, smoothing: int, boundary: set):
    """New boundary matching and the number of closed circles after one smoothing."""
    parent: dict = {}
    for p, q in matching:
        parent[p] = p
        parent[q] = p
    for s in slots:
        parent.setdefault(s, s)

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in SMOOTHINGS[smoothing]:
        ra, rb = find(slots[a]), find(slots[b])
        if ra != rb:
            parent[ra] = rb
    ends: dict = {}
    for x in parent:
        ends.setdefault(find(x), [])
    for x in boundary:
        if x in parent:
            ends[find(x)].append(x)
    closed, pairs = 0, []
    for group in ends.values():
        if not group:
            closed += 1
        elif len(group) == 2:
            pairs.append((group[0], group[1]) if group[0] < group[1] else (group[1], group[0]))
        else:
            raise ArithmeticError("a smoothing arc has neither zero nor two ends")
    # arcs of the old matching untouched by this crossing keep their pairs (they are in `ends`)
    pairs.sort()
    return tuple(pairs), closed


def jones_obstruction(diagram: Diagram, *, max_states: int | None = 4096,
                      max_transitions: int | None = 200_000, order=None,
                      check: Callable[[], None] = lambda: None) -> dict | None:
    """A witness that the Jones polynomial is nontrivial, or None (inconclusive).

    Raises FilterLimit when a budget is exhausted.
    """
    pd = diagram.pd
    if not pd:
        return None
    p, a = PRIME, JONES_A
    inv_a = pow(a, -1, p)
    delta = (-a * a - inv_a * inv_a) % p
    delta_powers = [1, delta, delta * delta % p, pow(delta, 3, p), pow(delta, 4, p)]
    order = best_scan_order(pd, tries=min(len(pd), 12)) if order is None else list(order)
    states: dict = {(): 1}
    boundary: set = set()
    peak, transitions = 1, 0
    for index in order:
        check()
        slots = pd[index]
        for e in slots:
            if e in boundary:
                boundary.remove(e)
            else:
                boundary.add(e)
        # a loop edge (both ends at this crossing) toggles twice and correctly stays out
        new: dict = {}
        for matching, coefficient in states.items():
            for smoothing, weight in ((0, a), (1, inv_a)):
                transitions += 1
                target, closed = _glue(matching, slots, smoothing, boundary)
                value = (new.get(target, 0) + coefficient * weight * delta_powers[closed]) % p
                if value:
                    new[target] = value
                else:
                    new.pop(target, None)
            if max_transitions is not None and transitions > max_transitions:
                raise FilterLimit("Jones transition budget exhausted")
            if max_states is not None and len(new) > max_states:
                raise FilterLimit("Jones frontier budget exhausted")
        states = new
        peak = max(peak, len(states))
    if boundary or any(states):
        raise ArithmeticError("the bracket scan ended with an open boundary")
    bracket = states.get((), 0)
    writhe = diagram.writhe()
    expected = delta * pow((-pow(a, 3, p)) % p, writhe % (p - 1), p) % p
    if bracket == expected:
        return None
    return {"kind": "kauffman-bracket-differs-from-unknot", "prime": p, "A": a, "writhe": writhe,
            "bracket": bracket, "unknot_bracket": expected, "peak_states": peak,
            "transitions": transitions}
