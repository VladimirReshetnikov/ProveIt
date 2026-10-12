"""Linear-time, exact certificates from the signed Seifert graph.

The input must be a validated classical one-component ``Diagram``.  Three
criteria are used:

* a genus-zero Seifert surface certifies the unknot;
* a homogeneous diagram realizes knot genus (Cromwell);
* the Kawamura--Lobb interval contains Rasmussen's s-invariant, so an interval
  excluding zero certifies a nontrivial knot.

Homogeneity is tested without block decomposition: Abe's criterion is
``circles + 1 == positive_components + negative_components``.  Isolated
vertices count as components in BOTH signed subgraphs.

References:
P. R. Cromwell, Homogeneous links, J. London Math. Soc. (2) 39 (1989), 535--552.
A. Lobb, Computable bounds for Rasmussen's concordance invariant,
    Compositio Math. 147 (2011), 661--668, Theorem 1.10; arXiv:0908.2745.
T. Abe, The Rasmussen invariant of a homogeneous knot,
    Proc. Amer. Math. Soc. 139 (2011), 2647--2656, Theorems 2.3 and 3.4;
    arXiv:1003.5392.

``verify_seifert_certificate`` independently reconstructs the orientation and
uses disjoint sets instead of the production circle/graph traversals.  It
does not trust cached orientation, signs, circle IDs, or component counts.
It shares the input Diagram validation and cited mathematical theorems.
"""
from __future__ import annotations


def _components(adjacency: list[list[int]]) -> int:
    seen = bytearray(len(adjacency))
    count = 0
    for start in range(len(adjacency)):
        if seen[start]:
            continue
        count += 1
        seen[start] = 1
        stack = [start]
        while stack:
            vertex = stack.pop()
            for neighbor in adjacency[vertex]:
                if not seen[neighbor]:
                    seen[neighbor] = 1
                    stack.append(neighbor)
    return count


def _summary(n: int, writhe: int, circles: int, positive: int, negative: int) -> dict:
    twice_genus = n - circles + 1
    defect = circles + 1 - positive - negative
    lower = writhe - circles + 2 * positive - 1
    upper = writhe + circles - 2 * negative + 1
    if twice_genus < 0 or twice_genus % 2 or defect < 0 or upper - lower != 2 * defect:
        raise ArithmeticError("inconsistent signed Seifert graph of a classical knot")
    return {
        "crossings": n,
        "writhe": writhe,
        "seifert_circles": circles,
        "positive_components": positive,
        "negative_components": negative,
        "homogeneity_defect": defect,
        "canonical_genus": twice_genus // 2,
        "rasmussen_interval": [lower, upper],
    }


def seifert_data(diagram) -> dict:
    """Return signed Seifert graph counts in O(n) word operations and memory.

    A PD row is counterclockwise, with under ports 0,2 and over ports 1,3.
    If u,o are the incoming ports, oriented smoothing pairs u with o+2 and
    o with u+2 (all port arithmetic is modulo four).
    """
    n = diagram.crossings
    if not n:
        return _summary(0, 0, 1, 1, 1)
    incoming = diagram.incoming_slots()
    alpha = diagram.alpha()
    smoothing = [0] * (4 * n)
    signs = []
    for crossing, (under, over) in enumerate(incoming):
        base = 4 * crossing
        for left, right in ((under, (over + 2) % 4), (over, (under + 2) % 4)):
            smoothing[base + left] = base + right
            smoothing[base + right] = base + left
        signs.append(1 if (over - under) % 4 == 3 else -1)
    owner = [-1] * (4 * n)
    circles = 0
    for start in range(4 * n):
        if owner[start] != -1:
            continue
        dart = start
        while owner[dart] == -1:
            mate = smoothing[dart]
            owner[dart] = owner[mate] = circles
            dart = alpha[mate]
        circles += 1
    positive = [[] for _ in range(circles)]
    negative = [[] for _ in range(circles)]
    for crossing, ((under, over), sign) in enumerate(zip(incoming, signs)):
        left, right = owner[4 * crossing + under], owner[4 * crossing + over]
        adjacency = positive if sign > 0 else negative
        adjacency[left].append(right)
        adjacency[right].append(left)
    return _summary(n, sum(signs), circles, _components(positive), _components(negative))


def seifert_certificate(diagram) -> dict | None:
    """Return an exact UNKNOT/KNOTTED certificate, or None if inconclusive.

    A zero Rasmussen interval alone never certifies the unknot.  In
    particular, homogeneous knots of positive genus with s=0 are KNOTTED.
    """
    data = seifert_data(diagram)
    lower, upper = data["rasmussen_interval"]
    if data["canonical_genus"] == 0:
        status, criterion = "UNKNOT", "seifert-genus-zero"
    elif data["homogeneity_defect"] == 0:
        status, criterion = "KNOTTED", "homogeneous-seifert-genus"
    elif lower > 0 or upper < 0:
        status, criterion = "KNOTTED", "rasmussen-interval"
    else:
        return None
    return {"version": 1, "status": status, "criterion": criterion, **data}


def verify_seifert_certificate(diagram, certificate: dict) -> bool:
    """Replay a certificate with a separate union-find implementation.

    This is an independent implementation of the sufficient condition, not
    a formal proof checker of the cited topological theorems.  Complexity is
    O(n alpha(n)) word operations with union by size and path compression.
    Malformed certificates return False.
    """
    if not isinstance(certificate, dict) or type(certificate.get("version")) is not int:
        return False
    if certificate["version"] != 1:
        return False
    n = len(diagram.pd)
    if not n:
        expected = {
            "crossings": 0, "writhe": 0, "seifert_circles": 1,
            "positive_components": 1, "negative_components": 1,
            "homogeneity_defect": 0, "canonical_genus": 0,
            "rasmussen_interval": [0, 0],
        }
    else:
        positions = {}
        paired = [0] * (4 * n)
        for crossing, row in enumerate(diagram.pd):
            for slot, label in enumerate(row):
                dart = 4 * crossing + slot
                other = positions.pop(label, None)
                if other is None:
                    positions[label] = dart
                else:
                    paired[dart], paired[other] = other, dart
        if positions:
            return False
        # Start at an arbitrary incoming dart and follow the knot component.
        enters = bytearray(4 * n)
        dart = 0
        for _ in range(2 * n):
            if enters[dart]:
                return False
            enters[dart] = 1
            opposite = 4 * (dart // 4) + ((dart % 4 + 2) % 4)
            dart = paired[opposite]
        if dart != 0:
            return False

        def disjoint_sets(size):
            parent = list(range(size))
            weights = [1] * size

            def find(item):
                while parent[item] != item:
                    parent[item] = parent[parent[item]]
                    item = parent[item]
                return item

            def union(left, right):
                left, right = find(left), find(right)
                if left == right:
                    return
                if weights[left] < weights[right]:
                    left, right = right, left
                parent[right] = left
                weights[left] += weights[right]

            return find, union

        find, union = disjoint_sets(4 * n)
        for dart, other in enumerate(paired):
            union(dart, other)
        under_ports, over_ports, signs = [], [], []
        for crossing in range(n):
            base = 4 * crossing
            under = 0 if enters[base] else 2
            over = 1 if enters[base + 1] else 3
            if sum(enters[base:base + 4]) != 2:
                return False
            union(base + under, base + ((over + 2) % 4))
            union(base + over, base + ((under + 2) % 4))
            under_ports.append(base + under)
            over_ports.append(base + over)
            signs.append(1 if over == (under - 1) % 4 else -1)
        roots = {find(dart) for dart in range(4 * n)}
        circle_id = {root: index for index, root in enumerate(roots)}
        circles = len(roots)
        plus_find, plus_union = disjoint_sets(circles)
        minus_find, minus_union = disjoint_sets(circles)
        for under, over, sign in zip(under_ports, over_ports, signs):
            left, right = circle_id[find(under)], circle_id[find(over)]
            if sign > 0:
                plus_union(left, right)
            else:
                minus_union(left, right)
        positive = len({plus_find(vertex) for vertex in range(circles)})
        negative = len({minus_find(vertex) for vertex in range(circles)})
        writhe = sum(signs)
        genus2 = n - circles + 1
        defect = circles + 1 - positive - negative
        if genus2 < 0 or genus2 % 2 or defect < 0:
            return False
        expected = {
            "crossings": n, "writhe": writhe, "seifert_circles": circles,
            "positive_components": positive, "negative_components": negative,
            "homogeneity_defect": defect, "canonical_genus": genus2 // 2,
            "rasmussen_interval": [writhe - circles + 2 * positive - 1,
                                   writhe + circles - 2 * negative + 1],
        }
    for key, value in expected.items():
        supplied = certificate.get(key)
        if isinstance(value, int):
            if type(supplied) is not int or supplied != value:
                return False
        elif type(supplied) is not list or len(supplied) != 2 or any(
                type(entry) is not int for entry in supplied) or supplied != value:
            return False
    lower, upper = expected["rasmussen_interval"]
    criterion = certificate.get("criterion")
    status = certificate.get("status")
    if criterion == "seifert-genus-zero":
        return status == "UNKNOT" and expected["canonical_genus"] == 0
    if criterion == "homogeneous-seifert-genus":
        return (status == "KNOTTED" and expected["canonical_genus"] > 0
                and expected["homogeneity_defect"] == 0)
    if criterion == "rasmussen-interval":
        return status == "KNOTTED" and (lower > 0 or upper < 0)
    return False
