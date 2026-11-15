#!/usr/bin/env python3
"""Generate a finite inner-box certificate at a specified, bounded mesh.

This optional frontend never trusts a claimed volume. It computes the actual
inner-box volume and calls the exact checker. The paper proves an explicit
sufficient mesh from independently justified volume and radius data.
"""

from fractions import Fraction as Q
from itertools import product
from math import ceil

from minkowski import parse_and_check, rational, require, vec


def from_grid(body: dict, mesh: int, normalized_radius) -> dict:
    n = body.get("dimension")
    require(type(n) is int and n > 0, "Positive dimension required")
    require(type(mesh) is int and mesh > 0, "Positive mesh required")
    radius = rational(normalized_radius)
    require(radius > 0, "Positive radius required")
    basis = tuple(vec(row, n) for row in body["basis"])
    require(len(basis) == n, "Incorrect basis shape")
    slabs = [(vec(s["normal"], n), rational(s["bound"])) for s in body["slabs"]]
    rows = [(tuple(2 * sum((a[i] * basis[i][k] for i in range(n)), Q(0))
                   for k in range(n)), b) for a, b in slabs]
    h = ceil(mesh * radius / 2) + 1

    def included(a):
        for row, bound in rows:
            low = sum((min(row[k] * a[k], row[k] * (a[k] + 1)) for k in range(n)), Q(0))
            high = sum((max(row[k] * a[k], row[k] * (a[k] + 1)) for k in range(n)), Q(0))
            if low < -mesh * bound or high > mesh * bound:
                return False
        return True

    # Coalesce contiguous cells in the first coordinate; the other coordinates
    # are single grid intervals. This is an exact finite dissection, not a
    # numerical approximation or a geometric library operation.
    boxes = []
    for tail in product(range(-h, h + 1), repeat=n - 1):
        run = None
        for first in range(-h, h + 2):
            good = first <= h and included((first, *tail))
            if good and run is None:
                run = first
            if not good and run is not None:
                lower = [Q(run, mesh), *(Q(t, mesh) for t in tail)]
                upper = [Q(first, mesh), *(Q(t + 1, mesh) for t in tail)]
                boxes.append({"lower": list(map(str, lower)), "upper": list(map(str, upper))})
                run = None
    result = {**body, "schema": "minkowski-ipra-boxes-v1", "boxes": boxes}
    parse_and_check(result)
    return result
