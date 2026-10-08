"""Certified visible connected-sum factorization through Gauss interlacement.

Exact visible factorization for the ``fastunknot`` package.  The historical
``factor.visible_factors`` API remains available for comparison and compatibility.

On a validated spherical, one-component PD diagram, connected components of
the Gauss-word interlacement graph are exactly the atoms of visible two-edge
cut factorization.  Components and a spanning-forest certificate are found in
O(n alpha(n)) time and O(n) space, without constructing the possibly quadratic
edge set.  Checked output construction costs O(n log n) overall because the
upstream ``Diagram.from_pd`` sorts edge labels.  Set ``validate=False`` only
when the input has already been validated; output construction is then linear.

This factors a *diagram*.  It does not find the prime factors of an arbitrary
knot diagram and does not make unknot recognition quasi-polynomial.
"""
from __future__ import annotations

from collections import defaultdict

from .diagram import Diagram


def _validated_word(word):
    word = tuple(word)
    if len(word) % 2:
        raise ValueError("a double-occurrence word has even length")
    n = len(word) // 2
    counts = [0] * n
    for x in word:
        if type(x) is not int or not 0 <= x < n:
            raise ValueError("crossings must be integers in 0..n-1")
        counts[x] += 1
    if any(c != 2 for c in counts):
        raise ValueError("every crossing must occur exactly twice")
    return word


class _UnionFind:
    def __init__(self, n):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x):
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != x:
            self.parent[x], x = root, self.parent[x]
        return root

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return a
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        return a


def interlacement_components(word):
    """Return (components, forest) for a normalized double-occurrence word.

    The forest contains actual alternating chord pairs and has exactly n-k
    edges.  Every component is ordered by original crossing number; components
    are ordered by their least crossing.  The algorithm works for arbitrary
    double-occurrence words, including words not realizable in the sphere.
    """
    word = _validated_word(word)
    n = len(word) // 2
    uf = _UnionFind(n)
    first = [-1] * n
    # Each active component owns a circular doubly linked list of its open
    # chords.  Lists concatenate and arbitrary chords delete in constant time.
    head = [-1] * n
    following = [-1] * n
    previous = [-1] * n
    stack = []
    forest = []
    for position, x in enumerate(word):
        if first[x] < 0:
            first[x] = position
            head[x] = following[x] = previous[x] = x
            stack.append(x)
            continue
        root = uf.find(x)
        while uf.find(stack[-1]) != root:
            other = uf.find(stack.pop())
            # All open chords of 'other' started after x.  Thus x and this
            # currently open representative are genuinely interlaced.
            forest.append((x, head[other]))
            a, b = head[root], head[other]
            last_a, last_b = previous[a], previous[b]
            following[last_a], previous[b] = b, last_a
            following[last_b], previous[a] = a, last_b
            root = uf.union(root, other)
            head[root] = a
        stack[-1] = root
        if following[x] == x:
            head[root] = -1
            stack.pop()
        else:
            a, b = previous[x], following[x]
            following[a], previous[b] = b, a
            if head[root] == x:
                head[root] = b
        following[x] = previous[x] = -1
    groups = defaultdict(list)
    for x in range(n):
        groups[uf.find(x)].append(x)
    return [tuple(group) for group in groups.values()], forest


def verify_interlacement_certificate(word, certificate):
    """Independently verify a component/forest certificate in O(n alpha(n)).

    Connectivity is witnessed by alternating pairs.  Separation is checked
    by a component nesting stack, without repeating the discovery algorithm.
    The verifier checks combinatorial decomposition only; the caller must
    establish that the input PD diagram is spherical and one-component.
    """
    word = _validated_word(word)
    n = len(word) // 2
    groups = certificate.get("crossing_components", ())
    forest = certificate.get("interlacement_forest", ())
    owner = [-1] * n
    for c, group in enumerate(groups):
        if not group:
            raise ValueError("empty interlacement component")
        for x in group:
            if type(x) is not int or not 0 <= x < n or owner[x] != -1:
                raise ValueError("components do not partition the crossings")
            owner[x] = c
    if any(c < 0 for c in owner):
        raise ValueError("components do not cover the crossings")
    if len(forest) != n - len(groups):
        raise ValueError("a spanning forest must have n-k edges")
    positions = [[] for _ in range(n)]
    for i, x in enumerate(word):
        positions[x].append(i)
    uf = _UnionFind(n)
    for edge in forest:
        if len(edge) != 2:
            raise ValueError("a forest edge must have two endpoints")
        x, y = edge
        if any(type(v) is not int or not 0 <= v < n for v in (x, y)):
            raise ValueError("invalid forest endpoint")
        a, b = positions[x]
        c, d = positions[y]
        if not (a < c < b < d or c < a < d < b):
            raise ValueError("a claimed forest edge is not interlaced")
        if owner[x] != owner[y] or uf.find(x) == uf.find(y):
            raise ValueError("forest crosses components or contains a cycle")
        uf.union(x, y)
    for group in groups:
        root = uf.find(group[0])
        if any(uf.find(x) != root for x in group):
            raise ValueError("forest does not connect a component")
    # Distinct actual components are nested in gaps of one another.  A visit
    # to an outer component cannot occur before a nested component finishes.
    counts = [0] * len(groups)
    stack = []
    for x in word:
        c = owner[x]
        if counts[c] == 0:
            stack.append(c)
        if not stack or stack[-1] != c:
            raise ValueError("distinct components interlace")
        counts[c] += 1
        if counts[c] == 2 * len(groups[c]):
            stack.pop()
    if stack:
        raise ValueError("incomplete component nesting")
    return True


def visible_factors_interlacement(diagram, check=lambda: None, *, validate=True):
    """Return visible factors and an independently checkable certificate.

    ``diagram`` must be a validated ``fastunknot.Diagram``.  The return shape
    intentionally differs from upstream ``visible_factors``: the second item
    is a certificate dictionary, not a list of recursive two-edge-cut records.
    The zero-crossing circle is returned as a single factor.
    """
    check()
    walk = diagram.traversal()
    word = tuple(d // 4 for d in walk)
    groups, forest = interlacement_components(word)
    certificate = {
        "algorithm": "gauss-interlacement-v1",
        "original_crossings": diagram.crossings,
        "crossing_components": [list(group) for group in groups],
        "interlacement_forest": [list(edge) for edge in forest],
    }
    if len(groups) <= 1:
        return [diagram], certificate
    n = diagram.crossings
    owner, local = [-1] * n, [-1] * n
    rows = []
    for c, group in enumerate(groups):
        check()
        rows.append([[-1] * 4 for _ in group])
        for k, x in enumerate(group):
            owner[x], local[x] = c, k
    visits = [0] * len(groups)
    last_dart = [-1] * len(groups)
    for dart in walk:
        x, slot = divmod(dart, 4)
        c = owner[x]
        row = rows[c][local[x]]
        row[slot] = visits[c]
        row[(slot + 2) % 4] = visits[c] + 1
        visits[c] += 1
        last_dart[c] = dart
    factors = []
    for c, component_rows in enumerate(rows):
        check()
        dart = last_dart[c]
        x, slot = divmod(dart, 4)
        component_rows[local[x]][(slot + 2) % 4] = 0
        factors.append(Diagram.from_pd(component_rows) if validate else
                       Diagram(tuple(tuple(row) for row in component_rows)))
    return factors, certificate

