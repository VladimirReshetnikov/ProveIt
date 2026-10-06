"""Two independent, exact, standard-library permutation-graph enumerators.

``enumerate_degree(n)`` adapts ``compute_rooted.py``, SHA256
``c2ae94aa6a9565606b9c4cf47224f533792991b7215c36849f84b09b02667dc7``.
That source uses degree-partition canonical graph masks and independently
canonicalizes root-colored graphs.

``enumerate_refined(n)`` separately adapts ``independent_enumeration.py``,
SHA256 ``6b3679f8c2a165232e8ab56963eb20a8103d0ea57dfc39efa9256a833c4c3371``.
That independently authored audit uses iterated color refinement, bit
adjacency, and root orbits obtained from all minimizing labelings.

The optional sampling/fiber extension is freshly authored atop these two
independent adapted routes. The earlier ``enumerate_one_realizer_inputs.py``
computation reused the refined audit's canonicalization primitives; it is
therefore not a third independent graph-enumeration method. Here method A
finds singleton root orbits by grouping separate root-colored canonical
keys, whereas method B reads orbit sizes from its minimizing labelings.

No original research file is imported or needed at run time. The two paths
below deliberately do not share graph construction, canonicalization, or
root counting code. Every permutation of the requested order is visited;
neither path samples graphs or uses tabulated answers. Default results have
only deterministic integer fields; optional sampling diagnostics also have
deterministically sorted integer lists. Orders 1 through 9 are the intended range;
larger positive orders remain exact but can require substantial resources.

Both adaptations eliminate redundant orders of interchangeable vertices
(true or false twins). Swapping twins is an explicitly verified graph
automorphism, so this is an exact reduction, not a heuristic. Method A
requires only a canonical minimum and root-colored isomorphism tests.
Method B restores the omitted twin permutations' factorial multiplicity and
unions their vertex orbits, retaining its distinct automorphism-based proof.
Input graphs are also cached only after an explicit relabeling: equality of
these labeled adjacency masks is a sufficient, exact isomorphism test.
"""

from collections import defaultdict
import itertools
import math


def _check_n(n):
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError("n must be a positive integer")


# -------------------------------------------------------------------------
# A: degree classes; triangular little-endian masks; separate root coloring.
# -------------------------------------------------------------------------

def _degree_mask(rows, order):
    """Source-A triangular edge order: (0,1),(0,2),(1,2),...."""
    result = 0
    bit = 1
    for j in range(1, len(order)):
        neighbors = rows[order[j]]
        for i in range(j):
            if neighbors & (1 << order[i]):
                result |= bit
            bit <<= 1
    return result


def _degree_blocks(rows, root=None):
    classes = defaultdict(list)
    for vertex, neighbors in enumerate(rows):
        classes[(vertex == root, neighbors.bit_count())].append(vertex)
    ordered = sorted(classes.items())
    signature = tuple((color, len(vertices)) for color, vertices in ordered)
    return signature, [vertices for _, vertices in ordered]


def _degree_twin_classes(rows, vertices):
    classes = []
    for vertex in vertices:
        for cell in classes:
            other = cell[0]
            if not ((rows[vertex] ^ rows[other])
                    & ~((1 << vertex) | (1 << other))):
                cell.append(vertex)
                break
        else:
            classes.append([vertex])
    return classes


def _degree_orders(rows, vertices):
    """All block orders modulo the verified within-twin permutations."""
    cells = _degree_twin_classes(rows, vertices)
    used = [0] * len(cells)
    order = []

    def visit():
        if len(order) == len(vertices):
            yield tuple(order)
            return
        for index, cell in enumerate(cells):
            if used[index] < len(cell):
                order.append(cell[used[index]])
                used[index] += 1
                yield from visit()
                used[index] -= 1
                order.pop()

    return tuple(visit())


def _degree_minimum(rows, groups, collect=False):
    possibilities = [_degree_orders(rows, vertices) for vertices in groups]
    best = None
    encountered = set() if collect else None
    for blocks in itertools.product(*possibilities):
        order = tuple(vertex for block in blocks for vertex in block)
        value = _degree_mask(rows, order)
        if best is None or value < best:
            best = value
        if collect:
            encountered.add(value)
    return best, encountered


def enumerate_degree(n, *, sampling=False):
    """Return ``dict(n=n, a=a_n, r=r_n, permutations=n!)`` using method A.

    A degree class fixes each vertex's label block. Exhaustive orders inside
    those blocks give an exact canonical minimum. A root is an extra color,
    so repeating the same computation with a distinguished vertex counts
    rooted isomorphism classes without using method B's automorphism code.

    The cache stores at most 250,000 degree-ordered labeled masks, including
    masks actually encountered during canonicalization. Each such mask is
    explicitly isomorphic to the canonical representative recorded for it.
    Filling the cache changes run time only. Root tests happen once per
    unrooted representative, and one root per twin class suffices because
    exchanging twins is an automorphism.

    If ``sampling=True``, count every graph's full permutation fiber ``f``.
    Add ``b`` (graphs with ``f=1``), ``c`` (singleton vertex orbits of those
    graphs), ``fiber_histogram`` (sorted ``fiber``/``graphs`` records), and
    sorted ``one_realizer_graphs`` witnesses. Witness ``realizer`` values and
    ``singleton_orbit_vertices`` positions are both one-based. The marked
    fiber of a rooted class is ``t = f * orbit_size``, so precisely these
    singleton orbits have ``t=1``. No extra diagnostics change the default
    return shape.
    """
    _check_n(n)
    representatives = {}
    cache = defaultdict(dict)
    cache_size = 0
    cache_limit = 250_000
    visited = 0
    fibers = {} if sampling else None
    first_realizers = {} if sampling else None

    for permutation in itertools.permutations(range(n)):
        visited += 1
        rows = [0] * n
        for j in range(1, n):
            for i in range(j):
                if permutation[i] > permutation[j]:
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
        signature, groups = _degree_blocks(rows)
        normalized = _degree_mask(
            rows, tuple(vertex for group in groups for vertex in group))
        known = cache[signature]
        if normalized in known:
            key = known[normalized]
        else:
            collect = cache_size < cache_limit
            best, encountered = _degree_minimum(rows, groups, collect)
            key = (signature, best)
            if collect:
                # Sorting makes bounded-cache behavior reproducible too.
                for value in sorted(encountered):
                    if cache_size >= cache_limit:
                        break
                    if value not in known:
                        known[value] = key
                        cache_size += 1
        if key not in representatives:
            representatives[key] = rows
            if sampling:
                first_realizers[key] = permutation
        if sampling:
            fibers[key] = fibers.get(key, 0) + 1

    rooted = 0
    witnesses = []
    for graph_key, rows in representatives.items():
        root_keys = {}
        for twins in _degree_twin_classes(rows, range(n)):
            root = twins[0]
            signature, groups = _degree_blocks(rows, root)
            best, _ = _degree_minimum(rows, groups)
            # Each member of the twin class has this same rooted type.
            root_keys.setdefault((signature, best), []).extend(twins)
        rooted += len(root_keys)
        if sampling and fibers[graph_key] == 1:
            witnesses.append({
                "realizer": [v + 1 for v in first_realizers[graph_key]],
                "singleton_orbit_vertices": sorted(
                    vertices[0] + 1 for vertices in root_keys.values()
                    if len(vertices) == 1)})
    result = {"n": n, "a": len(representatives), "r": rooted,
              "permutations": visited}
    if sampling:
        histogram = defaultdict(int)
        for fiber in fibers.values():
            histogram[fiber] += 1
        witnesses.sort(key=lambda witness: witness["realizer"])
        result.update({
            "b": len(witnesses),
            "c": sum(len(witness["singleton_orbit_vertices"])
                     for witness in witnesses),
            "fiber_histogram": [{"fiber": fiber, "graphs": histogram[fiber]}
                                for fiber in sorted(histogram)],
            "one_realizer_graphs": witnesses})
    return result


# -------------------------------------------------------------------------
# B: refined colors; big-endian row masks; minimizing-labeling root orbits.
# No graph construction, partition, canonicalization, or twin code from A.
# -------------------------------------------------------------------------

def _refined_inversion_graph(permutation):
    length = len(permutation)
    adjacency = [0 for _ in permutation]
    for left in range(length):
        for right in range(left + 1, length):
            if permutation[left] > permutation[right]:
                adjacency[left] += 1 << right
                adjacency[right] += 1 << left
    return adjacency


def _refined_partition(adjacency):
    n = len(adjacency)
    colors = [neighbors.bit_count() for neighbors in adjacency]
    while True:
        signatures = [
            (colors[v], tuple(sorted(colors[w] for w in range(n)
                                     if adjacency[v] >> w & 1)))
            for v in range(n)]
        color_map = {signature: color for color, signature
                     in enumerate(sorted(set(signatures)))}
        replacement = [color_map[signature] for signature in signatures]
        stable = len(set(replacement)) == len(set(colors))
        colors = replacement
        if stable:
            break
    return [[v for v in range(n) if colors[v] == color]
            for color in sorted(set(colors))]


def _refined_key(adjacency, order):
    result = 0
    for i, vertex in enumerate(order):
        for neighbor in order[i + 1:]:
            result = (result << 1) | ((adjacency[vertex] >> neighbor) & 1)
    return result


def _refined_canonical(adjacency, groups, orbit_sizes=False):
    """Canonical key, automorphism count, and number of vertex orbits.

    Relative orders of verified twins are fixed during enumeration. Every
    retained ordering represents exactly ``multiplicity`` full labelings.
    Twin transpositions plus maps between retained minimizing labelings
    generate precisely the same vertex orbits as the unabridged source.
    With ``orbit_sizes=True``, append a tuple giving the orbit size at each
    original vertex position. Such position-indexed data must not be reused
    under a different vertex labeling without an explicit relabeling.
    """
    n = len(adjacency)
    twin_pairs = []
    multiplicity = 1
    block_choices = []
    for group in groups:
        # A predecessor constraint chooses one order of each twin class.
        # This independently implements the symmetry reduction used here.
        predecessors = {}
        lengths = {}
        leaders = []
        for vertex in group:
            leader = next((u for u in leaders
                           if (adjacency[u] | (1 << u) | (1 << vertex))
                           == (adjacency[vertex] | (1 << u) | (1 << vertex))),
                          None)
            if leader is None:
                leaders.append(vertex)
                lengths[vertex] = [vertex]
            else:
                predecessors[vertex] = lengths[leader][-1]
                lengths[leader].append(vertex)
                twin_pairs.append((leader, vertex))
        for members in lengths.values():
            multiplicity *= math.factorial(len(members))

        choices = []

        def extend(prefix, remaining):
            if not remaining:
                choices.append(prefix)
                return
            for vertex in remaining:
                if predecessors.get(vertex) not in remaining:
                    extend(prefix + (vertex,), remaining - {vertex})

        # Integer set iteration is deterministic here, but canonical minima
        # and orbit counts do not depend on the traversal order in any case.
        extend((), set(group))
        block_choices.append(choices)

    parent = list(range(n))

    def find(vertex):
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def join(left, right):
        parent[find(left)] = find(right)

    best = None
    first = None
    automorphisms = 0
    for blocks in itertools.product(*block_choices):
        order = sum(blocks, ())
        key = _refined_key(adjacency, order)
        if best is None or key < best:
            best = key
            first = order
            automorphisms = multiplicity
            parent = list(range(n))
            for left, right in twin_pairs:
                join(left, right)
        elif key == best:
            automorphisms += multiplicity
            for left, right in zip(first, order):
                join(left, right)
    roots = [find(vertex) for vertex in range(n)]
    result = best, automorphisms, len(set(roots))
    if orbit_sizes:
        sizes = {root: roots.count(root) for root in set(roots)}
        return result + (tuple(sizes[root] for root in roots),)
    return result


def enumerate_refined(n, *, sampling=False):
    """Return ``dict(n=n, a=a_n, r=r_n, permutations=n!)`` using method B.

    Each permutation is visited and its inversion graph is color-refined.
    Exhaustive orders within final color classes produce the canonical key.
    The minimizing labelings supply automorphisms, whose vertex orbits count
    inequivalent roots. This path performs no root-colored canonicalization.
    Its cache is keyed by the complete adjacency mask after an explicit
    refined-color relabeling, never by a refinement signature alone.

    ``sampling=True`` adds ``b``, ``c``, ``fiber_histogram``, and sorted
    ``one_realizer_graphs`` with one-based ``realizer`` and
    ``singleton_orbit_vertices`` lists, exactly as in ``enumerate_degree``.
    Each graph's exhaustive fiber is counted during permutation traversal.
    Only one-realizer graphs need position-indexed orbit sizes; recomputing
    their minimizing labelings avoids reusing vertex indices from a cached
    isomorphic graph with a different labeling. Here ``t=f*orbit_size=1``
    is tested from automorphism orbits, independently of route A's root
    colorings.
    """
    _check_n(n)
    representatives = {}
    normalized_cache = {}
    visited = 0
    fiber_counts = {} if sampling else None
    unique_realizers = {} if sampling else None
    for permutation in itertools.permutations(range(n)):
        visited += 1
        adjacency = _refined_inversion_graph(permutation)
        groups = _refined_partition(adjacency)
        normalized = _refined_key(adjacency, sum(groups, []))
        result = normalized_cache.get(normalized)
        if result is None:
            result = _refined_canonical(adjacency, groups)
            normalized_cache[normalized] = result
        key, automorphisms, root_orbits = result
        if key not in representatives:
            representatives[key] = (automorphisms, root_orbits)
        if sampling:
            fiber_counts[key] = fiber_counts.get(key, 0) + 1
            if fiber_counts[key] == 1:
                unique_realizers[key] = permutation
            else:
                unique_realizers.pop(key, None)
    result = {"n": n, "a": len(representatives),
              "r": sum(value[1] for value in representatives.values()),
              "permutations": visited}
    if sampling:
        witnesses = []
        for permutation in sorted(unique_realizers.values()):
            graph = _refined_inversion_graph(permutation)
            detailed = _refined_canonical(
                graph, _refined_partition(graph), orbit_sizes=True)
            witnesses.append({
                "realizer": [v + 1 for v in permutation],
                "singleton_orbit_vertices": [position + 1 for position, size
                                             in enumerate(detailed[3])
                                             if size == 1]})
        distinct_fibers = sorted(set(fiber_counts.values()))
        result["b"] = len(witnesses)
        result["c"] = sum(len(witness["singleton_orbit_vertices"])
                          for witness in witnesses)
        result["fiber_histogram"] = [
            {"fiber": fiber,
             "graphs": sum(count == fiber for count in fiber_counts.values())}
            for fiber in distinct_fibers]
        result["one_realizer_graphs"] = witnesses
    return result


__all__ = ["enumerate_degree", "enumerate_refined"]
