"""Certified diagrammatic connected-sum cuts, NOT general prime decomposition.

A proper cyclic interval in the traversal with no singly visited crossing has
exactly two edges to its complement. Both sides are connected. This is a
2-edge bond in a spherical graph; its dual is a Jordan 2-cycle, so closing the
two sides gives a connected-sum decomposition. No prime-detection claim.
"""
from time import monotonic
from .diagram import Diagram


def split_once(diagram, *, deadline=None):
    n = diagram.crossings
    if n < 2:
        return None
    walk = diagram.traversal()
    labels = [d // 4 for d in walk]
    length = len(labels)
    best = None
    best_size = 0
    # Only intervals of at most half the traversal are needed: use complements.
    for start in range(length):
        if deadline is not None and monotonic() >= deadline:
            from .scan import ScanLimit
            raise ScanLimit("time budget exhausted in diagram factorisation")
        open_crossings = set()
        visited = set()
        for offset in range(n):
            crossing = labels[(start + offset) % length]
            visited.add(crossing)
            if crossing in open_crossings:
                open_crossings.remove(crossing)
            else:
                open_crossings.add(crossing)
            if not open_crossings and len(visited) > best_size:
                best = frozenset(visited)
                best_size = len(visited)
        if best_size == n // 2:
            break
    if best is None:
        return None
    # Recheck the separating edge pair, rather than trusting the search alone.
    in_counts = {}
    for i in best:
        for e in diagram.pd[i]:
            in_counts[e] = in_counts.get(e, 0) + 1
    cut = sorted(e for e, count in in_counts.items() if count == 1)
    if len(cut) != 2:
        raise ArithmeticError("candidate factor does not have a two-edge boundary")
    first, second = cut
    sides = []
    indices = []
    for inside in (True, False):
        ix = [i for i in range(n) if (i in best) == inside]
        rows = [tuple(first if e == second else e for e in diagram.pd[i]) for i in ix]
        sides.append(Diagram.from_pd(rows))
        indices.append(ix)
    return sides[0], sides[1], {"cut_edges": cut, "crossing_sets": indices}


def diagram_factors(diagram, *, deadline=None):
    """Return leaves and a replayable recursive two-edge-cut certificate."""
    leaves = []
    root = {}
    stack = [(diagram, root)]
    while stack:
        current, certificate = stack.pop()
        split = split_once(current, deadline=deadline)
        if split is None:
            certificate.update({"leaf": len(leaves), "crossings": current.crossings})
            leaves.append(current)
        else:
            left, right, proof = split
            certificate.update(proof)
            certificate["children"] = [{}, {}]
            stack.append((right, certificate["children"][1]))
            stack.append((left, certificate["children"][0]))
    return leaves, root


def connected_sum(diagrams):
    """Utility for reproducible benchmarks: splice one edge of each PD code."""
    result = Diagram.from_pd([])
    for other in diagrams:
        if not result.crossings:
            result = other
            continue
        if not other.crossings:
            continue
        left = [list(row) for row in result.pd]
        offset = 2 * result.crossings
        right = [[e + offset for e in row] for row in other.pd]
        left_darts = [(i, j) for i, row in enumerate(left) for j, e in enumerate(row) if e == 0]
        right_darts = [(i, j) for i, row in enumerate(right) for j, e in enumerate(row) if e == offset]
        i, j = left_darts[0]
        k, l = right_darts[0]
        left[i][j], right[k][l] = offset, 0
        result = Diagram.from_pd(left + right)
    return result


def replay_factor_certificate(diagram, certificate):
    """Validate a recursive two-edge-cut certificate and reconstruct its leaves.

    This checks diagram topology only, not the numerical homology of each leaf.
    Edge labels and crossing indices are local to the normalized PD at a node.
    Malformed or inconsistent certificates raise ValueError/DiagramError.
    """
    if not isinstance(certificate, dict):
        raise ValueError("factor certificate must be a dictionary")
    diagram = Diagram.from_pd(diagram.pd)
    leaves = []
    stack = [(diagram, certificate)]
    while stack:
        current, node = stack.pop()
        if not isinstance(node, dict):
            raise ValueError("factor certificate node must be a dictionary")
        n = current.crossings
        if 'leaf' in node:
            if (type(node['leaf']) is not int or node['leaf'] != len(leaves)
                    or type(node.get('crossings')) is not int or node['crossings'] != n
                    or 'children' in node):
                raise ValueError("invalid factor leaf")
            leaves.append(current)
            continue
        sides = node.get('crossing_sets')
        children = node.get('children')
        cut = node.get('cut_edges')
        if (not isinstance(sides, list) or len(sides) != 2
                or not isinstance(children, list) or len(children) != 2
                or not isinstance(cut, list) or len(cut) != 2
                or any(type(e) is not int for e in cut) or cut[0] >= cut[1]):
            raise ValueError("invalid factor split record")
        if any(not isinstance(side, list) or not side
               or any(type(i) is not int for i in side) for side in sides):
            raise ValueError("invalid crossing sets")
        flattened = sides[0] + sides[1]
        if len(flattened) != n or set(flattened) != set(range(n)):
            raise ValueError("crossing sets do not partition the diagram")
        counts = {}
        for i in sides[0]:
            for e in current.pd[i]:
                counts[e] = counts.get(e, 0) + 1
        if sorted(e for e, c in counts.items() if c == 1) != cut:
            raise ValueError("asserted cut is not the two-edge boundary")
        first, second = cut
        closed = [Diagram.from_pd([
            tuple(first if e == second else e for e in current.pd[i])
            for i in side]) for side in sides]
        # Diagram validation also rules out a disconnected side after closing.
        stack.append((closed[1], children[1]))
        stack.append((closed[0], children[0]))
    return leaves
