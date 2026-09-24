"""Exact largest-simplex calculations for series-parallel posets.

Python 3.10+, standard library only. No floating-point geometric computation.
The sole float value is -inf, used as an impossible-state sentinel.
An expression is 'x', ('S', left, right), or ('P', left, right).
S means ordinal sum (left below right); P means disjoint union.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Iterator, Sequence

NEG = float('-inf')
Number = int | float
Matrix = tuple[Number, Number, Number, Number]
Expr = str | tuple[str, 'Expr', 'Expr']
LEAF: Matrix = (-1, 0, 0, 1)
STATES: tuple[Matrix, ...] = (
    (-2, -1, -1, 0), (-1, -1, -1, 0), (-1, -1, 0, 0),
    (-1, 0, -1, 0), (-1, 0, 0, NEG), (-1, 0, 0, 0),
    (0, 0, 0, NEG), (0, 0, 0, 0),
)
KAPPA = (4, 4, 3, 3, 2, 3, 3, 2)


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def series_matrix(a: Matrix, b: Matrix) -> Matrix:
    return tuple(max(a[2+j] + b[2*i+1], a[j] + b[2*i] + 1)
                 for i in (0, 1) for j in (0, 1))  # type: ignore


def parallel_matrix(a: Matrix, b: Matrix, na: int, nb: int) -> Matrix:
    if min(na, nb) < 1:
        raise ValueError('Both factors must be nonempty.')
    return (max(0, *a[:3], *b[:3], max(a) if nb >= 2 else NEG,
                max(b) if na >= 2 else NEG),
            max(a[1], a[3], b[1], b[3]),
            max(a[2], a[3], b[2], b[3]), NEG)


@dataclass(frozen=True)
class Invariants:
    n: int
    matrix: Matrix
    height: int
    avoiding_origin: int

    @property
    def order_simplex(self) -> int:
        return int(max(self.matrix))

    @property
    def chain_simplex(self) -> int:
        return max(self.height, self.avoiding_origin)

    @property
    def state(self) -> int:
        s = self.order_simplex
        normalized = tuple(v-s for v in self.matrix)
        return STATES.index(normalized) + 1

    @property
    def gap(self) -> int:
        return self.chain_simplex - self.order_simplex


def combine(op: str, a: Invariants, b: Invariants) -> Invariants:
    if op == 'S':
        return Invariants(a.n+b.n, series_matrix(a.matrix, b.matrix),
                          a.height+b.height, a.avoiding_origin+b.avoiding_origin+1)
    if op == 'P':
        return Invariants(a.n+b.n, parallel_matrix(a.matrix, b.matrix, a.n, b.n),
                          max(a.height, b.height),
                          max(a.height, a.avoiding_origin, b.height, b.avoiding_origin))
    raise ValueError('Operation must be S or P.')


def evaluate(expr: Expr) -> Invariants:
    """Iterative postorder evaluation: no recursion limit or tuple hashing.

    The time bound is linear in the expanded expression-tree node count.
    A shared subtree is evaluated once per occurrence, not as a compressed DAG.
    """
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    values: list[Invariants] = []
    while stack:
        node, visited = stack.pop()
        if node == 'x':
            values.append(Invariants(1, LEAF, 1, 0))
            continue
        if not isinstance(node, tuple) or len(node) != 3 or node[0] not in ('S', 'P'):
            raise ValueError('An expression must be x, (S, left, right), or (P, left, right).')
        if visited:
            right, left = values.pop(), values.pop()
            values.append(combine(node[0], left, right))
        else:
            stack.extend(((node, True), (node[2], False), (node[1], False)))
    return values[0]


def fold(op: str, expressions: Sequence[Expr]) -> Expr:
    if not expressions:
        raise ValueError('At least one expression is required.')
    ans = expressions[0]
    for expr in expressions[1:]:
        ans = (op, ans, expr)
    return ans


def antichain_expr(n: int) -> Expr:
    if not isinstance(n, int) or n < 1:
        raise ValueError('Antichain size must be a positive integer.')
    return fold('P', ['x'] * n)


def layered_expr(sizes: Sequence[int]) -> Expr:
    return fold('S', [antichain_expr(a) for a in sizes])


def layered_formula(sizes: Sequence[int]) -> tuple[int, int, int]:
    """Return (s_O, s_C, nu) via independent-set counts on a conflict path."""
    if not sizes or any(not isinstance(a, int) or a < 1 for a in sizes):
        raise ValueError('A nonempty sequence of positive integers is required.')
    eligible = [i for i in range(len(sizes)-1) if min(sizes[i:i+2]) >= 2]
    nu, run, previous = 0, 0, -2
    for edge in eligible:
        if edge == previous+1 and sizes[edge] == 2:
            run += 1
        else:
            nu += (run+1)//2
            run = 1
        previous = edge
    nu += (run+1)//2
    r = len(sizes)
    k = sum(a >= 2 for a in sizes)
    return r+nu, r+max(0, k-1), nu


# Finite posets are tuples of strict upper-set bitmasks on 0,...,n-1.
Poset = tuple[int, ...]


def from_expr(expr: Expr) -> Poset:
    if expr == 'x':
        return (0,)
    op, left, right = expr
    a, b = from_expr(left), from_expr(right)
    n = len(a)
    cross = ((1 << len(b))-1) << n if op == 'S' else 0
    return tuple(m | cross for m in a) + tuple(m << n for m in b)


def predecessors(p: Poset) -> Poset:
    pred = [0] * len(p)
    for i, upper in enumerate(p):
        for j in bits(upper):
            pred[j] |= 1 << i
    return tuple(pred)


def natural_posets(n: int) -> Iterator[Poset]:
    """Every transitive relation contained in the natural linear order, once."""
    if n < 0:
        raise ValueError('n must be nonnegative.')
    if n == 0:
        yield ()
        return
    for p in natural_posets(n-1):
        pred = predecessors(p)
        for down in range(1 << (n-1)):
            if all(pred[j] & ~down == 0 for j in bits(down)):
                yield tuple(upper | ((1 << (n-1)) if down >> i & 1 else 0)
                            for i, upper in enumerate(p)) + (0,)


def components(adjacency: Sequence[int]) -> list[int]:
    remaining = (1 << len(adjacency))-1
    result = []
    while remaining:
        reached = remaining & -remaining
        frontier = reached
        while frontier:
            neighbors = 0
            for i in bits(frontier):
                neighbors |= adjacency[i]
            frontier = neighbors & remaining & ~reached
            reached |= frontier
        remaining &= ~reached
        result.append(reached)
    return result


def induced(p: Poset, subset: int) -> Poset:
    labels = list(bits(subset))
    return tuple(sum(1 << j for j, oldj in enumerate(labels) if p[oldi] >> oldj & 1)
                 for oldi in labels)


def decompose(p: Poset) -> Expr | None:
    """Recognize an SP poset; the returned expression may relabel its elements."""
    n = len(p)
    if not n:
        raise ValueError('Only nonempty posets are supported.')
    if n == 1:
        return 'x'
    pred = predecessors(p)
    comp = tuple(p[i] | pred[i] for i in range(n))
    chunks = components(comp)
    op = 'P'
    if len(chunks) == 1:
        allbits = (1 << n)-1
        chunks = components(tuple(allbits & ~(comp[i] | (1 << i)) for i in range(n)))
        op = 'S'
        if len(chunks) == 1:
            return None
        # All pairs from distinct incomparability components are comparable.
        # Sorting by number of predecessor components determines their order.
        unordered_chunks = chunks[:]
        chunks.sort(key=lambda c: sum(bool(pred[next(bits(c))] & d)
                                      for d in unordered_chunks if d != c))
    sub = [decompose(induced(p, c)) for c in chunks]
    if any(e is None for e in sub):
        return None
    return fold(op, sub)  # type: ignore


def vertices(p: Poset, kind: str) -> list[int]:
    if kind == 'O':
        return [m for m in range(1 << len(p))
                if all(p[i] & ~m == 0 for i in bits(m))]
    if kind == 'C':
        return [m for m in range(1 << len(p))
                if all(p[i] & m == 0 for i in bits(m))]
    raise ValueError('kind must be O or C.')


# Inequalities are (coefficient vector, rhs), interpreted as a.x <= rhs.
Inequality = tuple[tuple[int, ...], int]


def inequalities(p: Poset, kind: str) -> list[Inequality]:
    n = len(p)
    result: list[Inequality] = []
    for i in range(n):
        result.append((tuple(-int(i == j) for j in range(n)), 0))
    if kind == 'O':
        for i in range(n):
            result.append((tuple(int(i == j) for j in range(n)), 1))
            for j in bits(p[i]):
                result.append((tuple(int(k == i)-int(k == j) for k in range(n)), 0))
    elif kind == 'C':
        pred = predecessors(p)
        comp = tuple(p[i] | pred[i] for i in range(n))
        for m in range(1, 1 << n):
            if all((m & ~(1 << i)) & ~comp[i] == 0 for i in bits(m)):
                # Only maximal chains are needed.
                if not any(all(comp[j] >> i & 1 for i in bits(m))
                           for j in range(n) if not m >> j & 1):
                    result.append((tuple(int(m >> j & 1) for j in range(n)), 1))
    else:
        raise ValueError('kind must be O or C.')
    return result


def affine_rank(points: Sequence[int], n: int) -> int:
    if not points:
        return -1
    base = points[0]
    rows = [[Fraction((v >> j & 1)-(base >> j & 1)) for j in range(n)]
            for v in points[1:]]
    rank = 0
    for col in range(n):
        pivot = next((k for k in range(rank, len(rows)) if rows[k][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivotval = rows[rank][col]
        rows[rank] = [x/pivotval for x in rows[rank]]
        for k in range(rank+1, len(rows)):
            if rows[k][col]:
                factor = rows[k][col]
                rows[k] = [x-factor*y for x, y in zip(rows[k], rows[rank])]
        rank += 1
    return rank


def maximum_clique(adjacency: Sequence[int], required: int = 0,
                   forbidden: int = 0) -> int | None:
    """An exact branch-and-bound solver, returning a vertex bitmask."""
    if required & forbidden:
        return None
    req = list(bits(required))
    if any(not adjacency[i] >> j & 1 for i, j in combinations(req, 2)):
        return None
    possible = ((1 << len(adjacency))-1) & ~(required | forbidden)
    for i in req:
        possible &= adjacency[i]
    best, best_size = required, required.bit_count()

    def expand(chosen: int, candidates: int, size: int) -> None:
        nonlocal best, best_size
        if size+candidates.bit_count() <= best_size:
            return
        if not candidates:
            if size > best_size:
                best, best_size = chosen, size
            return
        # A proper greedy coloring supplies clique upper bounds.
        order, bounds = [], []
        left, color = candidates, 0
        while left:
            color += 1
            independent = left
            while independent:
                bit = independent & -independent
                v = bit.bit_length()-1
                order.append(v)
                bounds.append(color)
                left ^= bit
                independent &= ~bit & ~adjacency[v]
        for index in range(len(order)-1, -1, -1):
            if size+bounds[index] <= best_size:
                return
            v = order[index]
            bit = 1 << v
            next_chosen = chosen | bit
            next_candidates = candidates & adjacency[v]
            if size+1 > best_size:
                best, best_size = next_chosen, size+1
            expand(next_chosen, next_candidates, size+1)
            candidates &= ~bit
    expand(required, possible, best_size)
    return best


def geometric_check(p: Poset, kind: str) -> dict:
    """Independently optimize using the exact defining inequalities.

    Edges are recovered from intersections of common tight inequalities.
    No SP recurrence or poset edge/clique characterization is used here.
    Every optimizing clique is separately certified to be a simplex face.
    """
    verts = vertices(p, kind)
    ineqs = inequalities(p, kind)
    tight_vertices = [0] * len(ineqs)
    tight_at = [0] * len(verts)
    for vindex, v in enumerate(verts):
        for j, (a, rhs) in enumerate(ineqs):
            lhs = sum(a[k] for k in bits(v))
            assert lhs <= rhs
            if lhs == rhs:
                tight_at[vindex] |= 1 << j
                tight_vertices[j] |= 1 << vindex
    allverts = (1 << len(verts))-1

    def face_from_common(common: int) -> int:
        face = allverts
        for j in bits(common):
            face &= tight_vertices[j]
        return face

    adjacency = [0] * len(verts)
    pair_checks = 0
    for i, j in combinations(range(len(verts)), 2):
        face = face_from_common(tight_at[i] & tight_at[j])
        pair_checks += 1
        if face == (1 << i) | (1 << j):
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i

    zero = 1 << verts.index(0)
    states = []
    if kind == 'O':
        one = 1 << verts.index((1 << len(p))-1)
        for i in (0, 1):
            for j in (0, 1):
                states.append(((zero if i else 0) | (one if j else 0),
                               (zero if not i else 0) | (one if not j else 0)))
    else:
        states = [(zero, 0), (0, zero)]
    answers, witnesses = [], []
    for required, forbidden in states:
        clique = maximum_clique(adjacency, required, forbidden)
        if clique is None:
            answers.append(NEG)
            witnesses.append(None)
            continue
        if not clique:
            answers.append(-1)
            witnesses.append({'vertices': [], 'dimension': -1,
                              'active_inequalities': [], 'empty_face': True})
            continue
        common = (1 << len(ineqs))-1
        for vindex in bits(clique):
            common &= tight_at[vindex]
        actualface = face_from_common(common)
        assert actualface == clique, ('maximum clique is not a face', p, kind, clique)
        points = [verts[i] for i in bits(clique)]
        dimension = affine_rank(points, len(p))
        assert dimension == len(points)-1, ('face not affinely independent', p, kind)
        answers.append(dimension)
        witnesses.append({'vertices': [list(bits(v)) for v in points],
                          'dimension': dimension,
                          'active_inequalities': [{'a': ineqs[i][0], 'rhs': ineqs[i][1]}
                                                  for i in bits(common)]})
    return {'values': answers, 'witnesses': witnesses, 'pair_checks': pair_checks,
            'vertices': len(verts), 'inequalities': len(ineqs)}
