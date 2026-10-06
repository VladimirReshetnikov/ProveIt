#!/usr/bin/env python3
"""Exact, finite verification for Report150; not a proof of asymptotics.

Python 3.10+ standard library only. All mathematical checks use explicit
exceptions, never assert, and therefore remain active under python -O.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import re
from safe_io import fresh_file, regular_bytes

ROOT = Path(__file__).resolve().parent
PRIME_CORE = (0, 1, 2, 0, 3, 1, 4, 2, 5, 4, 3, 5)
NONPRIME_ASYMMETRIC_DIAGRAM = (0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 4, 5)
SCHEMA = 'report150-exact-checks-v1'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(x):
    x = Fraction(x)
    return {'numerator': x.numerator, 'denominator': x.denominator}


@lru_cache(None)
def matching_number(n):
    require(type(n) is int and n >= 0, 'Matching index must be a nonnegative integer')
    return 1 if n == 0 else (2 * n - 1) * matching_number(n - 1)


def matchings(vertices):
    """Every matching exactly once, with the least remaining endpoint first."""
    if not vertices:
        yield ()
        return
    first = vertices[0]
    for j in range(1, len(vertices)):
        for tail in matchings(vertices[1:j] + vertices[j + 1:]):
            yield ((first, vertices[j]),) + tail


def normalize(word):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in word)


def word_from_matching(edges, endpoint_count=None):
    size = 2 * len(edges) if endpoint_count is None else endpoint_count
    out = [None] * size
    for label, (a, b) in enumerate(edges):
        require(out[a] is None and out[b] is None, 'Repeated endpoint')
        out[a] = out[b] = label
    require(None not in out, 'Unmatched endpoint')
    return tuple(out)


def dihedral_images(word):
    """Full D_(2n) action, including all rotations and both orientations."""
    w = tuple(word)
    return tuple(normalize(v[i:] + v[:i]) for v in (w, w[::-1]) for i in range(len(w)))


def dihedral_info(word):
    w = normalize(word)
    images = dihedral_images(w)
    orbit = set(images)
    stabilizer = images.count(w)
    require(len(orbit) * stabilizer == 2 * len(w), 'Orbit-stabilizer failure')
    return min(orbit), len(orbit), stabilizer


def adjacency(word):
    """Intersection graph: endpoints alternate exactly when chords cross."""
    places = defaultdict(list)
    for i, value in enumerate(word):
        places[value].append(i)
    require(set(places) == set(range(len(places))), 'Chord labels must be consecutive')
    require(all(len(v) == 2 for v in places.values()), 'Not a double-occurrence word')
    out = [0] * len(places)
    for a, b in combinations(range(len(out)), 2):
        left, right = places[a]
        x, y = places[b]
        if (left < x < right) != (left < y < right):
            out[a] |= 1 << b
            out[b] |= 1 << a
    return tuple(out)


def degree_signature(graph):
    return tuple(sorted(x.bit_count() for x in graph))


def connected(graph):
    if not graph:
        return True
    seen, todo = 1, [0]
    while todo:
        new = graph[todo.pop()] & ~seen
        seen |= new
        while new:
            bit = new & -new
            todo.append(bit.bit_length() - 1)
            new ^= bit
    return seen == (1 << len(graph)) - 1


def degree_orders(graph):
    cells = defaultdict(list)
    for i, row in enumerate(graph):
        cells[row.bit_count()].append(i)
    for choices in product(*(permutations(cells[d]) for d in sorted(cells))):
        yield tuple(v for block in choices for v in block)


@lru_cache(None)
def canonical_graph(graph):
    """Exact isomorphism key, minimizing within sorted degree cells."""
    best = None
    n = len(graph)
    for order in degree_orders(graph):
        code = 0
        for i in range(n):
            for j in range(i + 1, n):
                code = (code << 1) | ((graph[order[i]] >> order[j]) & 1)
        if best is None or code < best:
            best = code
    return degree_signature(graph), best


def automorphism_count(graph):
    """Exhaust all degree-preserving bijections; test every adjacency."""
    original = tuple(sorted(range(len(graph)), key=lambda i: graph[i].bit_count()))
    count = 0
    for order in degree_orders(graph):
        mapping = dict(zip(original, order))
        if all(((graph[a] >> b) & 1) == ((graph[mapping[a]] >> mapping[b]) & 1)
               for a, b in combinations(range(len(graph)), 2)):
            count += 1
    return count


def split_partitions(graph):
    """All nontrivial splits, represented by the side containing vertex zero."""
    n, out = len(graph), []
    full = (1 << len(graph)) - 1
    for side in range(1, full):
        if not side & 1 or not 2 <= side.bit_count() <= n - 2:
            continue
        other = full ^ side
        nonempty_rows = {graph[v] & other for v in range(n) if side >> v & 1 and graph[v] & other}
        if len(nonempty_rows) <= 1:
            out.append([v for v in range(n) if side >> v & 1])
    return out


def expand_word(core, decorations):
    """Apply L/T/F at distinct core vertices, retaining all chord labels.

    decorations is a list (vertex, type, endpoint_choice). The endpoint choice
    is used only for L; it specifies the first/second occurrence in core.
    T inserts in equal order at both ends; F reverses the second order.
    """
    n = len(core) // 2
    require(len({x[0] for x in decorations}) == len(decorations), 'Repeated decorated vertex')
    selected = {v: (kind, endpoint, n + i) for i, (v, kind, endpoint) in enumerate(decorations)}
    seen, out = Counter(), []
    for vertex in core:
        occurrence = seen[vertex]
        seen[vertex] += 1
        if vertex not in selected:
            out.append(vertex)
            continue
        kind, endpoint, new = selected[vertex]
        require(kind in ('L', 'T', 'F'), 'Unknown decoration')
        if kind == 'L':
            require(endpoint in (0, 1), 'Invalid parent endpoint')
            out.extend((new, vertex, new) if occurrence == endpoint else (vertex,))
        elif kind == 'T' or occurrence == 0:
            out.extend((vertex, new))
        else:
            out.extend((new, vertex))
    return tuple(out)


def expected_decorated_graph(core_graph, decorations):
    """Independent graph-level construction, without using chord endpoints."""
    n, k = len(core_graph), len(decorations)
    blocks = {v: [v] for v in range(n)}
    leaves, internal = [], []
    for i, (v, kind, _) in enumerate(decorations):
        w = n + i
        if kind == 'L':
            leaves.append((v, w))
        else:
            blocks[v].append(w)
            if kind == 'T':
                internal.append((v, w))
    out = [0] * (n + k)
    edges = leaves + internal
    for a, b in combinations(range(n), 2):
        if core_graph[a] >> b & 1:
            edges.extend(product(blocks[a], blocks[b]))
    for a, b in edges:
        out[a] |= 1 << b
        out[b] |= 1 << a
    return tuple(out)


def remove_vertices(graph, removed):
    keep = [v for v in range(len(graph)) if v not in removed]
    return tuple(sum(1 << j for j, w in enumerate(keep) if graph[v] >> w & 1) for v in keep)


def twin_pairs(graph):
    return [(a, b, 'T' if graph[a] >> b & 1 else 'F')
            for a, b in combinations(range(len(graph)), 2)
            if (graph[a] & ~(1 << b)) == (graph[b] & ~(1 << a))]


def recover_decorated_graph(graph):
    """Finite canonical deletion/contraction check for the supplied examples."""
    leaves = [v for v, row in enumerate(graph) if row.bit_count() == 1]
    keep = [v for v in range(len(graph)) if v not in leaves]
    reduced = remove_vertices(graph, set(leaves))
    roots = list(range(len(reduced)))
    def root(v):
        while roots[v] != v:
            v = roots[v]
        return v
    for a, b, _ in twin_pairs(reduced):
        roots[root(b)] = root(a)
    grouped = defaultdict(list)
    for v in range(len(reduced)):
        grouped[root(v)].append(v)
    blocks = sorted(grouped.values(), key=min)
    require(all(len(block) <= 2 for block in blocks), 'Unexpected large twin class')
    vertex_to_block = {keep[v]: i for i, block in enumerate(blocks) for v in block}
    quotient = [0] * len(blocks)
    for a, b in combinations(range(len(blocks)), 2):
        values = {(reduced[v] >> w) & 1 for v in blocks[a] for w in blocks[b]}
        require(len(values) == 1, 'Quotient edge not well defined')
        if 1 in values:
            quotient[a] |= 1 << b
            quotient[b] |= 1 << a
    types = []
    for i, block in enumerate(blocks):
        if len(block) == 2:
            a, b = block
            types.append((i, 'T' if reduced[a] >> b & 1 else 'F'))
    for leaf in leaves:
        parent = graph[leaf].bit_length() - 1
        types.append((vertex_to_block[parent], 'L'))
    require(len({v for v, _ in types}) == len(types), 'Overlapping recovered decorations')
    return tuple(quotient), sorted(types), [[keep[v] for v in block] for block in blocks]


def rotation_fixed_formula(n, order):
    require((2 * n) % order == 0, 'Rotation order must divide endpoint count')
    k = 2 * n // order
    total = 0
    for pairs in range(k // 2 + 1):
        singles = k - 2 * pairs
        if singles and order % 2:
            continue
        total += factorial(k) * order ** pairs // (factorial(singles) * 2 ** pairs * factorial(pairs))
    return total


def symmetry_records(n, words):
    size = 2 * n
    observed = [0] * (2 * size)
    nontrivial = 0
    for word in words:
        images = dihedral_images(word)
        fixed = [i for i, image in enumerate(images) if image == word]
        for i in fixed:
            observed[i] += 1
        nontrivial += len(fixed) > 1
    from math import gcd
    predictions = [rotation_fixed_formula(n, size // gcd(size, shift)) for shift in range(size)]
    # w[::-1] then shift maps j to size-1-shift-j; parity determines fixed endpoints.
    for shift in range(size):
        fixed_endpoints = sum((size - 1 - shift - j) % size == j for j in range(size))
        reduced = n if fixed_endpoints == 0 else n - 1
        predictions.append(rotation_fixed_formula(reduced, 2) if reduced else 1)
    require(observed == predictions, 'Direct and formula symmetry counts disagree')
    require(sum(observed) % (4 * n) == 0, 'Burnside sum not integral')
    return {'n': n, 'fixed_counts_action_order': 'rotations 0..2n-1; reverse-then-rotate 0..2n-1',
            'observed_fixed_counts': observed, 'formula_fixed_counts': predictions,
            'symmetric_matchings': nontrivial, 'dihedral_orbits': sum(observed) // (4 * n)}


def small_enumeration():
    rows, symmetries = [], []
    for n in range(1, 7):
        words = [word_from_matching(m) for m in matchings(tuple(range(2 * n)))]
        require(len(words) == matching_number(n), 'Matching enumeration missed a diagram')
        fibers, is_connected = Counter(), {}
        for word in words:
            graph = adjacency(word)
            key = canonical_graph(graph)
            fibers[key] += 1
            is_connected[key] = connected(graph)
        reciprocal_sum = sum((Fraction(1, fibers[canonical_graph(adjacency(w))]) for w in words), Fraction())
        require(reciprocal_sum == len(fibers), 'Exact graph fiber sum failed')
        row = {'n': n, 'matchings': len(words), 'all_graphs': len(fibers),
               'connected_graphs': sum(is_connected.values()),
               'fiber_size_histogram': [[size, count] for size, count in sorted(Counter(fibers.values()).items())],
               'sum_matching_reciprocal_graph_fiber': rational(reciprocal_sum)}
        rows.append(row)
        symmetries.append(symmetry_records(n, words))
    return rows, symmetries


def long_leaf_checks():
    rows = []
    for n in range(3, 8):
        for r in range(1, (n - 2) // 2 + 1):
            chord = (0, 2 * r + 2)
            remaining = tuple(v for v in range(2 * n) if v not in chord)
            count = 0
            for tail in matchings(remaining):
                graph = adjacency(word_from_matching((chord,) + tail))
                count += graph[0].bit_count() == 1
            expanded = (2 * r + 1) * (2 * n - 2 * r - 3) * matching_number(r) * matching_number(n - r - 2)
            simplified = matching_number(r + 1) * matching_number(n - r - 1)
            require(count == expanded == simplified, 'Fixed long-leaf formula failed')
            rows.append({'n': n, 'r': r, 'fixed_leaf_endpoints': list(chord),
                         'enumerated_count': count, 'endpoint_choice_formula': expanded,
                         'double_factorial_formula': simplified})
    ratios = []
    for n in (8, 16, 32, 64, 128):
        q = {s: Fraction(matching_number(s) * matching_number(n - s), matching_number(n))
             for s in range(2, n // 2 + 1)}
        for s in range(2, n // 2):
            require(q[s + 1] / q[s] == Fraction(2 * s + 1, 2 * n - 2 * s - 1), 'Convolution ratio failed')
        bound = 2 * n * sum(q.values(), Fraction())
        endpoint_bound = 2 * n * (q[2] + n * q[3])
        require(bound <= endpoint_bound, 'Finite endpoint convolution bound failed')
        ratios.append({'n': n, 'expected_nonshort_leaves_upper_bound': rational(bound),
                       'endpoint_sum_upper_bound': rational(endpoint_bound)})
    return {'fixed_chord_counts': rows, 'convolution_checks': ratios}


def leaf_orbit_checks():
    graph = adjacency(PRIME_CORE)
    require(connected(graph) and min(row.bit_count() for row in graph) >= 2, 'Core hypothesis failed')
    require(not split_partitions(graph) and automorphism_count(graph) == 1, 'Core is not asymmetric split-prime')
    require(dihedral_info(PRIME_CORE)[2] == 1, 'Core diagram is symmetric')
    experiments = []
    for parents in ((0,), (0, 3), (0, 3, 5)):
        keys, records = set(), []
        for choices in product((0, 1), repeat=len(parents)):
            decorations = [(v, 'L', side) for v, side in zip(parents, choices)]
            word = expand_word(PRIME_CORE, decorations)
            result = adjacency(word)
            require(result == expected_decorated_graph(graph, decorations), 'Leaf movement changed the graph')
            key, orbit_size, stabilizer = dihedral_info(word)
            require(stabilizer == 1 and orbit_size == 4 * (6 + len(parents)), 'Expanded diagram not asymmetric')
            require(key not in keys, 'Independent leaf moves merged dihedral orbits')
            keys.add(key)
            records.append({'choices': list(choices), 'word': list(word), 'canonical_dihedral_word': list(key),
                            'dihedral_orbit_size': orbit_size, 'dihedral_stabilizer_order': stabilizer})
        experiments.append({'parents': list(parents), 'leaf_count': len(parents),
                            'distinct_constructed_dihedral_orbits': len(keys),
                            'constructed_indexed_representations': sum(x['dihedral_orbit_size'] for x in records),
                            'moves': records})
    # Full graph fiber on seven chords, not just the 2^k constructed subfamily.
    target = adjacency(expand_word(PRIME_CORE, [(0, 'L', 0)]))
    target_key = canonical_graph(target)
    orbit_hist, fiber_size = Counter(), 0
    for matching in matchings(tuple(range(14))):
        word = word_from_matching(matching)
        g = adjacency(word)
        if degree_signature(g) == degree_signature(target) and canonical_graph(g) == target_key:
            fiber_size += 1
            orbit_hist[dihedral_info(word)[0]] += 1
    require(fiber_size == 56 and sorted(orbit_hist.values()) == [28, 28], 'Seven-chord full fiber changed')
    require(set(orbit_hist) == {tuple(v['canonical_dihedral_word']) for v in experiments[0]['moves']}, 'Constructed and full fibers disagree in the explicit example')
    return {'core_word': list(PRIME_CORE), 'core_adjacency_bitmasks': list(graph),
            'core_nontrivial_split_count': len(split_partitions(graph)), 'core_graph_automorphism_order': automorphism_count(graph),
            'core_dihedral_stabilizer_order': dihedral_info(PRIME_CORE)[2],
            'independent_leaf_moves': experiments,
            'full_fiber_seven_chords': {'enumerated_all_indexed_matchings': matching_number(7),
                'graph_fiber_size': fiber_size, 'dihedral_orbit_count': len(orbit_hist),
                'orbit_sizes': sorted(orbit_hist.values()), 'graph_automorphism_order': automorphism_count(target),
                'scope': 'Exact equality here is finite evidence only; the general upper proof needs only a fiber lower bound.'}}


def decoration_checks():
    core_graph = adjacency(PRIME_CORE)
    examples = []
    for types in (('L',), ('T',), ('F',), ('L', 'T', 'F'), ('T', 'T', 'F')):
        decorations = [(v, kind, 0) for v, kind in zip((0, 3, 5), types)]
        word = expand_word(PRIME_CORE, decorations)
        graph = adjacency(word)
        require(graph == expected_decorated_graph(core_graph, decorations), 'Chord and graph decorations disagree')
        leaves = [v for v, row in enumerate(graph) if row.bit_count() == 1]
        require(len(leaves) == types.count('L'), 'Unexpected leaves')
        reduced = remove_vertices(graph, set(leaves))
        pairs = twin_pairs(reduced)
        require(sorted(t for _, _, t in pairs) == sorted(t for t in types if t != 'L'), 'Twin recovery failed')
        recovered_core, recovered_types, recovered_blocks = recover_decorated_graph(graph)
        require(recovered_core == core_graph, 'Canonical core recovery failed')
        require(recovered_types == sorted((v, kind) for v, kind, _ in decorations), 'Decoration vertex/type recovery failed')
        twin_swap_generators = []
        for i, (v, kind, _) in enumerate(decorations):
            if kind == 'L':
                continue
            w = 6 + i
            mapping = list(range(len(graph)))
            mapping[v], mapping[w] = w, v
            require(all(((graph[a] >> b) & 1) == ((graph[mapping[a]] >> mapping[b]) & 1)
                        for a, b in combinations(range(len(graph)), 2)), 'Twin swap not an automorphism')
            twin_swap_generators.append([v, w])
        aut = automorphism_count(graph)
        expected_aut = 2 ** (types.count('T') + types.count('F'))
        require(aut == expected_aut, 'Decorated graph automorphism formula failed')
        examples.append({'types': list(types), 'word': list(word), 'leaf_vertices': leaves,
                         'recovered_twin_pairs_after_leaf_deletion': [list(p) for p in pairs],
                         'graph_automorphism_order': aut, 'expected_graph_automorphism_order': expected_aut,
                         'independent_twin_swap_generators': twin_swap_generators,
                         'recovered_core_adjacency_bitmasks': list(recovered_core),
                         'recovered_vertex_type_decorations': [list(t) for t in recovered_types],
                         'recovered_blocks_before_contraction': recovered_blocks,
                         'dihedral_stabilizer_order_of_this_representation': dihedral_info(word)[2]})
    special = adjacency(NONPRIME_ASYMMETRIC_DIAGRAM)
    require(dihedral_info(NONPRIME_ASYMMETRIC_DIAGRAM)[2] == 1 and automorphism_count(special) > 1,
            'Geometry versus graph automorphism counterexample failed')
    coefficients = []
    for k in range(7):
        triple_sum = sum((Fraction(1, 2 ** k * factorial(l) * factorial(t) * factorial(k-l-t))
                          for l in range(k + 1) for t in range(k-l+1)), Fraction())
        require(triple_sum == Fraction(3, 2) ** k / factorial(k), 'Poisson multinomial coefficient failed')
        coefficients.append({'deficit': k, 'sum_triple_coefficients': rational(triple_sum),
                             'poisson_three_halves_coefficient': rational(Fraction(3, 2) ** k / factorial(k))})
    finite_weights = []
    for n in (20, 50, 100):
        for k in range(5):
            weight = Fraction(3 ** k * comb(n-k, k) * n * matching_number(n-k), (n-k) * matching_number(n))
            finite_weights.append({'n': n, 'k': k, 'exact_decoration_weight_relative_to_h_n': rational(weight),
                                   'limiting_coefficient_without_e_minus_three': rational(Fraction(3, 2) ** k / factorial(k))})
    return {'explicit_decorations': examples,
            'geometric_asymmetry_does_not_imply_graph_asymmetry': {
                'word': list(NONPRIME_ASYMMETRIC_DIAGRAM),
                'dihedral_stabilizer_order': dihedral_info(NONPRIME_ASYMMETRIC_DIAGRAM)[2],
                'graph_automorphism_order': automorphism_count(special),
                'nontrivial_split_count': len(split_partitions(special))},
            'poisson_deficit_coefficients': coefficients, 'finite_decoration_weights': finite_weights}


def atomic_pattern_checks():
    """Finite n=6 checks only; the Palm/Stein estimate is proved in the report."""
    n, size = 6, 12
    edge = lambda a, b: tuple(sorted((a, b)))
    cycle = [edge(i, (i+1) % size) for i in range(size)]
    patterns = {'X': [(e,) for e in cycle],
                'Y': [(edge(i, (i+2) % size),) for i in range(size)], 'Z': []}
    for first, second in combinations(cycle, 2):
        if set(first) & set(second):
            continue
        a, b = first
        c, d = second
        patterns['Z'].append(tuple(sorted((edge(a, c), edge(b, d)))))
        patterns['Z'].append(tuple(sorted((edge(a, d), edge(b, c)))))
    require(len(patterns['Z']) == len(set(patterns['Z'])) == size*(size-3), 'Duplicated or missing Z pattern')
    diagrams = [frozenset(m) for m in matchings(tuple(range(size)))]
    means = {}
    for kind, family in patterns.items():
        total_indicators = sum(sum(all(e in diagram for e in pattern) for pattern in family) for diagram in diagrams)
        measured = Fraction(total_indicators, len(diagrams))
        require(measured == Fraction(size, size-1), 'Atomic-pattern mean formula failed')
        means[kind] = {'pattern_count': len(family), 'total_indicators': total_indicators,
                       'exact_mean': rational(measured)}
    def force(diagram, pattern):
        result = set(diagram)
        for u, v in pattern:
            if edge(u, v) in result:
                continue
            mates = {a: b for a, b in result} | {b: a for a, b in result}
            x, y = mates[u], mates[v]
            result.remove(edge(u, x))
            result.remove(edge(v, y))
            result.add(edge(u, v))
            result.add(edge(x, y))
        return frozenset(result)
    witnesses = []
    for pattern in (((0, 1),), ((0, 2),), ((0, 3), (1, 4))):
        support = {v for e in pattern for v in e}
        preimages = Counter()
        unchanged = 0
        for diagram in diagrams:
            output = force(diagram, pattern)
            require(set(pattern) <= output, 'Forcing missed a target edge')
            require(all(e in output for e in diagram if not set(e) & support), 'Forcing destroyed an original outside-support edge')
            require(len(output) == n and {v for e in output for v in e} == set(range(size)), 'Forcing did not produce a matching')
            preimages[output] += 1
            unchanged += output == diagram
        targets = {diagram for diagram in diagrams if set(pattern) <= diagram}
        expected_multiplicity = 1
        for j in range(len(pattern)):
            expected_multiplicity *= size-2*j-1
        require(set(preimages) == targets, 'Forcing omitted a conditional target')
        require(set(preimages.values()) == {expected_multiplicity}, 'Conditional forcing preimages not equal')
        witnesses.append({'forced_pattern': [list(e) for e in pattern],
                          'target_matchings': len(targets), 'preimages_per_target': expected_multiplicity,
                          'observed_preimage_multiplicities': sorted(set(preimages.values())),
                          'fixed_input_matchings': unchanged, 'outside_support_edges_preserved': True})
    return {'n': n, 'all_indexed_matchings_examined': len(diagrams),
            'atomic_means': means, 'raw_Z_pattern_count': len(patterns['Z']),
            'distinct_Z_pattern_count': len(set(patterns['Z'])), 'forcing_witnesses': witnesses,
            'scope': 'All order-six matchings, three specified singleton/two-edge forcing witnesses. This does not computationally certify the asymptotic TV bound.'}


def poly_add(*polys):
    out = defaultdict(Fraction)
    for p in polys:
        for exponent, coefficient in p.items():
            out[exponent] += coefficient
    return {a: b for a, b in out.items() if b}


def poly_mul(a, b):
    out = defaultdict(Fraction)
    for (i, j), c in a.items():
        for (k, l), d in b.items():
            out[(i+k, j+l)] += c*d
    return {a: b for a, b in out.items() if b}


def encode_poly(poly):
    return [{'log_2u_power': i, 'log_2_power': j, 'coefficient': rational(c)}
            for (i, j), c in sorted(poly.items())]


def inverse_checks():
    # Formal monomials D^i c^j, with D=log(2u), c=log 2.
    delta = {(0, 0): Fraction(1), (-1, 0): Fraction(3, 2), (-1, 1): Fraction(1, 2)}
    constant_residual = poly_add(poly_mul({(1, 0): Fraction(1)}, delta),
                                {(1, 0): Fraction(-1), (0, 0): Fraction(-3, 2), (0, 1): Fraction(-1, 2)})
    require(not constant_residual, 'Inverse bounded-displacement cancellation failed')
    residual_first = poly_add(poly_mul({(0, 0): Fraction(1, 2)}, poly_mul(delta, delta)),
                              poly_mul({(0, 0): Fraction(-1)}, delta), {(0, 0): Fraction(-1, 24)})
    expected_first = {(0, 0): Fraction(-13, 24), (-2, 0): Fraction(9, 8),
                      (-2, 1): Fraction(3, 4), (-2, 2): Fraction(1, 8)}
    require(residual_first == expected_first, 'Inverse first omitted model term failed')
    # Expand the shifted Stirling formula using only rational power-series algebra.
    gamma_coeff = {}
    for power in range(1, 5):
        from_shifted_log = Fraction((-1) ** power, (power + 1) * 2 ** (power + 1))
        from_B2 = Fraction((-1) ** (power-1), 12 * 2 ** (power-1))
        from_B4 = Fraction(0)
        if power >= 3:
            from_B4 = Fraction(-((-1) ** (power-3)) * comb(power-1, 2), 360 * 2 ** (power-3))
        gamma_coeff[power] = from_shifted_log + from_B2 + from_B4
    require(gamma_coeff == {1: Fraction(-1, 24), 2: Fraction(0), 3: Fraction(7, 2880), 4: Fraction(0)},
            'Shifted gamma-model Stirling coefficients failed')
    # Exact threshold example on the same integer model, common constant suppressed.
    n = 20
    H = lambda j: Fraction(matching_number(j), j)
    a = lambda j: H(j) * Fraction(j-1, j)
    x = H(n) * Fraction(2*n-1, 2*n)
    B = Fraction(n, n-1)
    require(H(n-1) < x < H(n) and a(n) < x < a(n+1), 'Ceiling counterexample failed')
    require(H(n-1) < x/B <= H(n) < B*x < H(n+1), 'Exact ceiling-safe bracket failed')
    return {'symbols': {'D': 'log(2u)', 'c': 'log(2)'},
            'bounded_displacement': encode_poly(delta),
            'order_one_residual': encode_poly(constant_residual),
            'coefficient_of_one_over_u_in_logH_residual': encode_poly(residual_first),
            'gamma_log_remainder_coefficients': [{'one_over_t_power': j, 'coefficient': rational(c)} for j, c in gamma_coeff.items()],
            'ceiling_safety_example': {'model': 'H_j=(2j-1)!!/j, a_j=H_j(1-1/j), j>=2; common constant suppressed',
                'n': n, 'x_over_H_n': rational(x/H(n)), 'multiplicative_envelope_B': rational(B),
                'ceil_smooth_inverse_of_x': n, 'actual_least_index': n+1,
                'lower_safe_ceiling': n, 'upper_safe_ceiling': n+1,
                'purpose': 'Exact example showing a_n/H_n -> 1 alone does not justify an unqualified single ceiling.'},
            'scope': 'Formal inverse algebra concerns the smooth gamma model. It supplies no quantitative error rate for either graph sequence.'}


def source_checks(enumeration):
    snapshot = json.loads(regular_bytes(ROOT/'sources/oeis_snapshot.json'))
    oeis = {e['number']: [int(x) for x in e['data'].split(',')] for e in snapshot}
    require(set(oeis) == {156808, 156809}, 'Wrong source sequence identifiers')
    require(all(e['offset'].split(',')[0] == '1' for e in snapshot), 'Source offset changed')
    table = []
    for line in regular_bytes(ROOT/'sources/danielsen_parker_table3.txt').decode('utf-8').splitlines():
        pieces = line.split()
        if len(pieces) == 5 and all(re.fullmatch(r'[0-9,]+', s) for s in pieces):
            table.append([int(x.replace(',', '')) for x in pieces])
    require([row[0] for row in table] == list(range(1, 13)), 'Table 3 row parse failed')
    require([row[1] for row in table] == oeis[156808], 'Connected OEIS/Table 3 mismatch')
    require([row[2] for row in table] == oeis[156809][:12], 'All OEIS/Table 3 mismatch')
    for row in enumeration:
        require(row['connected_graphs'] == oeis[156808][row['n']-1], 'Independent connected enumeration disagrees')
        require(row['all_graphs'] == oeis[156809][row['n']-1], 'Independent all enumeration disagrees')
    # Unlabeled graphs are multisets of their connected components.
    limit = len(oeis[156808])
    euler = [1] + [0] * limit
    for size, count in enumerate(oeis[156808], 1):
        next_coeff = [0] * (limit+1)
        for j, value in enumerate(euler):
            for multiplicity in range((limit-j)//size+1):
                next_coeff[j+size*multiplicity] += value * comb(count+multiplicity-1, multiplicity)
        euler = next_coeff
    require(euler[1:] == oeis[156809][:limit], 'Connected-to-all Euler transform failed')
    # Independent inverse via the logarithmic derivative of the Euler product:
    # n*g_n = sum_{k=1}^n b_k*g_(n-k), b_k = sum_{d|k} d*c_d.
    all_with_empty = [1] + oeis[156809]
    logarithmic_derivative = [0] * len(all_with_empty)
    recovered_connected = [0] * len(all_with_empty)
    for n in range(1, len(all_with_empty)):
        logarithmic_derivative[n] = n*all_with_empty[n] - sum(
            logarithmic_derivative[k]*all_with_empty[n-k] for k in range(1, n))
        numerator = logarithmic_derivative[n] - sum(
            d*recovered_connected[d] for d in range(1, n) if n % d == 0)
        require(numerator % n == 0, 'Euler inversion failed integrality')
        recovered_connected[n] = numerator // n
    require(recovered_connected[1:13] == oeis[156808], 'Independent Euler inversion disagrees with source')
    require(recovered_connected[13] == 21593488017, 'Derived order-13 connected count changed')
    correction = []
    for n in range(2, limit+1):
        all_n, conn_n, prev = oeis[156809][n-1], oeis[156808][n-1], oeis[156809][n-2]
        remainder = all_n-conn_n-prev
        bound = sum(oeis[156809][k-1]*oeis[156809][n-k-1] for k in range(2, n//2+1))
        require(0 <= remainder <= bound, 'Disconnected-without-isolates inequality failed')
        correction.append({'n': n, 'disconnected_count': all_n-conn_n,
                           'graphs_with_an_isolate': prev, 'disconnected_without_isolates': remainder,
                           'component_product_upper_bound': bound})
    return {'sequence_ids': {'connected': 'A156808', 'all': 'A156809'},
            'offset': 1, 'connected_counts_through_12': oeis[156808],
            'all_counts_through_13': oeis[156809],
            'table3_agrees_through': 12, 'independent_enumeration_agrees_through': 6,
            'euler_transform_all_counts_including_empty': euler,
            'independent_euler_inversion_connected_counts_through_13': recovered_connected[1:],
            'derived_connected_count_order_13': {'value': recovered_connected[13],
                'status': 'Derived from A156809 by exact Euler inversion; not an entry in Danielsen-Parker Table 3 or the captured A156808 snapshot.'},
            'connectivity_correction_finite_counts': correction,
            'snapshot_sha256': {p.name: hashlib.sha256(regular_bytes(p)).hexdigest() for p in sorted((ROOT/'sources').glob('*')) if p.is_file()}}


@lru_cache(None)
def build_evidence():
    enumeration, symmetries = small_enumeration()
    return {'schema': SCHEMA,
            'scope': 'Exact finite computational checks, not a proof, convergence-rate certificate, or novelty certificate.',
            'arithmetic': 'Integer and fractions.Fraction; no numerical approximations in evidence.',
            'small_graph_enumeration': enumeration,
            'symmetry_formula_checks': symmetries,
            'long_leaf_formula_checks': long_leaf_checks(),
            'leaf_moves_and_graph_fibers': leaf_orbit_checks(),
            'decorations_poisson_and_automorphisms': decoration_checks(),
            'inverse_model_checks': inverse_checks(),
            'atomic_patterns_and_palm_forcing': atomic_pattern_checks(),
            'source_count_checks': source_checks(enumeration)}


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'evidence.json')
    args = parser.parse_args()
    result = build_evidence()
    fresh_file(args.output, (json.dumps(result, sort_keys=True, indent=2) + '\n').encode('utf-8'))
    print('Wrote exact deterministic evidence to ' + str(args.output))


if __name__ == '__main__':
    main()
