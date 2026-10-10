"""Complete polynomial recognition on K4-minor-free knot projections.

Rué--Thilikos--Velona, arXiv:1806.07855v3, Theorem 9 classifies these
knots as connected sums of T(2,q), q odd. Consequently determinant one
is sufficient here, after certifying the projection's treewidth <= 2.
It is never sufficient without this graph certificate.

The graph test uses O(n) operations. The signed Tait determinant uses
articulation blocks and exact Bareiss elimination, with polynomial bit
cost; this does NOT implement the stronger linear recognition algorithm
of Bodlaender--Burton--Fomin--Grigoriev (arXiv:1904.03117).
Input has the usual validated classical, one-component Diagram contract.
"""
from collections import deque


def _eliminate(adjacency, check):
    """Consume a simple graph, returning a width-two fill order or None."""
    queue = deque(v for v, neighbors in enumerate(adjacency) if len(neighbors) <= 2)
    alive = bytearray([1]) * len(adjacency)
    order = []
    while queue:
        check()
        vertex = queue.popleft()
        if not alive[vertex]:
            continue
        neighbors = sorted(adjacency[vertex])
        if len(neighbors) > 2:
            raise ArithmeticError("degree increased in width-two elimination")
        alive[vertex] = 0
        order.append(vertex)
        for neighbor in neighbors:
            adjacency[neighbor].remove(vertex)
        if len(neighbors) == 2:
            left, right = neighbors
            adjacency[left].add(right)
            adjacency[right].add(left)
        adjacency[vertex].clear()
        for neighbor in neighbors:
            if len(adjacency[neighbor]) <= 2:
                queue.append(neighbor)
    return order if len(order) == len(adjacency) else None


def projection_order(diagram, *, check=lambda: None):
    """Certify treewidth <= 2 of the crossing graph, ignoring edge multiplicity.

    This is the projection graph, NOT the checkerboard/Tait graph. Loops
    and parallel arcs do not affect its exclusion of a K4 minor.
    Failure means only that this particular diagram is outside the class.
    """
    check()
    adjacency = [set() for _ in diagram.pd]
    first = {}
    for vertex, row in enumerate(diagram.pd):
        check()
        for label in row:
            if label in first:
                other = first.pop(label)
                if other != vertex:
                    adjacency[vertex].add(other)
                    adjacency[other].add(vertex)
            else:
                first[label] = vertex
    return _eliminate(adjacency, check)


def exact_determinant(diagram, *, check=lambda: None):
    """Absolute signed tree sum of a Tait graph, including exact cancellation.

    Choose the shading with fewer vertices. Multiplication across blocks
    avoids one large dense cofactor on visibly composite diagrams. A zero
    pivot triggers row exchange in Bareiss; it never means inconclusive.
    """
    from .potts import _checkerboard, _tait_from_faces
    from .integer_determinant import bareiss
    from .tait_blocks import spanning_tree_product

    check()
    if not diagram.pd:
        return 1
    dart_face, colors = _checkerboard(diagram, check)
    shade = 0 if colors.count(0) <= colors.count(1) else 1
    vertices, edges = _tait_from_faces(diagram.crossings, dart_face, colors, shade)
    # The Potts omission exponent is the Goeritz incidence sign, up to a
    # global sign. The absolute cofactor determinant removes that ambiguity.
    stats = dict(tait_disconnected=0, tait_blocks=0, tait_bridge_factors=0,
                 max_cofactor_size=0, tait_block_determinants=0, tait_zero_factors=0)
    def tick(amount=1):
        check()
    result = abs(spanning_tree_product(vertices, edges, tick, bareiss, stats))
    check()
    return result


def treewidth_two_certificate(diagram, *, check=lambda: None):
    """Return a complete verdict on the certified class, else None.

    Cancellation propagates. No partial order or determinant is a verdict.
    The determinant is hex-encoded to support arbitrary-size JSON output.
    """
    order = projection_order(diagram, check=check)
    if order is None:
        return None
    determinant = exact_determinant(diagram, check=check)
    if not determinant % 2:
        raise ArithmeticError("a classical knot has odd determinant")
    check()
    return dict(version=1, method="treewidth-two-determinant",
                status="UNKNOT" if determinant == 1 else "KNOTTED",
                crossings=diagram.crossings, order=order,
                determinant_hex=hex(determinant))


def verify_treewidth_two_certificate(diagram, certificate, *, check=lambda: None):
    """Independently replay width and an exact Fox determinant.

    Uses an edge-set fill replay, uncached Wirtinger arc traversal and
    rational Gaussian elimination, rather than the producer's adjacency
    queue, checkerboard graph and integer Bareiss elimination. Shares the
    imported classification theorem and the Diagram input contract.
    """
    from fractions import Fraction

    check()
    if type(certificate) is not dict or set(certificate) != {
            "version", "method", "status", "crossings", "order", "determinant_hex"}:
        return False
    n = len(diagram.pd)
    if (type(certificate["version"]) is not int or certificate["version"] != 1
            or certificate["method"] != "treewidth-two-determinant"
            or type(certificate["crossings"]) is not int or certificate["crossings"] != n):
        return False
    order = certificate["order"]
    if (type(order) is not list or len(order) != n
            or any(type(v) is not int for v in order) or set(order) != set(range(n))):
        return False
    positions = {}
    for vertex, row in enumerate(diagram.pd):
        check()
        for label in row:
            positions.setdefault(label, []).append(vertex)
    edges = {tuple(sorted(ends)) for ends in positions.values() if ends[0] != ends[1]}
    for vertex in order:
        check()
        incident = {edge for edge in edges if vertex in edge}
        neighbors = {u for edge in incident for u in edge if u != vertex}
        if len(neighbors) > 2:
            return False
        edges.difference_update(incident)
        if len(neighbors) == 2:
            edges.add(tuple(sorted(neighbors)))

    # At t=-1 every Fox row is 2*over - under_1 - under_2,
    # independently of crossing sign and orientation.
    graph = {label: set() for label in positions}
    for _, b, _, d in diagram.pd:
        graph[b].add(d)
        graph[d].add(b)
    owner, columns = {}, 0
    for label in graph:
        check()
        if label in owner:
            continue
        stack = [label]
        owner[label] = columns
        while stack:
            check()
            for other in graph[stack.pop()]:
                if other not in owner:
                    owner[other] = columns
                    stack.append(other)
        columns += 1
    if n and columns != n:
        return False
    size = max(0, n - 1)
    matrix = []
    for a, b, c, _ in diagram.pd[:-1]:
        check()
        row = [Fraction(0)] * size
        for label, coefficient in ((b, 2), (a, -1), (c, -1)):
            if owner[label] < size:
                row[owner[label]] += coefficient
        matrix.append(row)
    determinant = Fraction(1)
    for k in range(size):
        check()
        pivot = next((i for i in range(k, size) if matrix[i][k]), None)
        if pivot is None:
            return False
        if pivot != k:
            matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
            determinant = -determinant
        value = matrix[k][k]
        determinant *= value
        nonzero = [j for j in range(k + 1, size) if matrix[k][j]]
        for i in range(k + 1, size):
            check()
            factor = matrix[i][k] / value
            if factor:
                for j in nonzero:
                    matrix[i][j] -= factor * matrix[k][j]
                matrix[i][k] = Fraction(0)
    if determinant.denominator != 1:
        return False
    value = abs(determinant.numerator)
    check()
    return (certificate["determinant_hex"] == hex(value)
            and certificate["status"] == ("UNKNOT" if value == 1 else "KNOTTED"))
