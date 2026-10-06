#!/usr/bin/env python3
"""Independent exact, standard-library checks for labeled cylindrical kings.

The geometric algorithm never uses binary words, block thresholds, run lengths,
or a spectral approximation. All checks use executable guards (also under -O).
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def matmul(a, b):
    require(bool(a) and bool(b) and len(a[0]) == len(b), "matrix shape")
    out = [[0] * len(b[0]) for _ in a]
    for i, row in enumerate(a):
        for k, value in enumerate(row):
            if value:
                for j, other in enumerate(b[k]):
                    if other:
                        out[i][j] += value * other
    return out


def transpose(a):
    return [list(c) for c in zip(*a)]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def traces(a, maximum):
    power = identity(len(a))
    out = []
    for _ in range(maximum):
        power = matmul(power, a)
        out.append(sum(power[i][i] for i in range(len(a))))
    return out


def geometric_counts(max_h, w):
    """Maximum-cardinality row DP directly on a 2*max_h by 2*w cylinder."""
    width = 2 * w
    # Enumerate row configurations by choosing actual column positions.
    masks = []
    for count in range(w + 1):
        for columns in combinations(range(width), count):
            if all(min(abs(a-b), width-abs(a-b)) > 1
                   for a, b in combinations(columns, 2)):
                masks.append(sum(1 << c for c in columns))
    full = (1 << width) - 1
    neighborhoods = {}
    for mask in masks:
        left = ((mask << 1) & full) | (mask >> (width - 1))
        right = (mask >> 1) | ((mask & 1) << (width - 1))
        neighborhoods[mask] = mask | left | right
    successors = {old: [new for new in masks
                        if not (old & neighborhoods[new])] for old in masks}
    # Keep the best attainable cardinality and its exact multiplicity at each row.
    states = {0: (0, 1)}
    answers = {}
    for rows in range(1, 2 * max_h + 1):
        next_states = {}
        for old, (score, count) in states.items():
            for new in successors[old]:
                value = score + new.bit_count()
                previous = next_states.get(new)
                if previous is None or value > previous[0]:
                    next_states[new] = (value, count)
                elif value == previous[0]:
                    next_states[new] = (value, previous[1] + count)
        states = next_states
        if rows % 2 == 0:
            maximum = max(v[0] for v in states.values())
            answers[rows // 2] = (maximum, sum(v[1] for v in states.values()
                                              if v[0] == maximum))
    return answers, {"width_columns": width, "legal_row_masks": len(masks),
                     "compatible_ordered_pairs": sum(map(len, successors.values()))}


def subset_count(h, w):
    """Brute subsets of squares, tested by pairwise cylindrical distances."""
    width = 2 * w
    cells = tuple(product(range(2 * h), range(width)))
    count = 0
    for placement in combinations(cells, h * w):
        if all(abs(r-s) > 1 or min(abs(c-d), width-abs(c-d)) > 1
               for (r, c), (s, d) in combinations(placement, 2)):
            count += 1
    return count


def binary_transition(bits):
    """Threshold rule, without constructing color components or geometry."""
    n = len(bits) + 1
    matrix = [[1] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if u < v:
                matrix[u][v] = int(not any(bits[i] > bits[i+1]
                                             for i in range(u, v-1)))
            elif v < u:
                matrix[u][v] = int(not any(bits[i] < bits[i+1]
                                             for i in range(v, u-1)))
    return matrix


def color_components(bits, color):
    """Connected components by explicit disjoint-set union of path vertices."""
    parent = list(range(len(bits) + 1))
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for edge, value in enumerate(bits):
        if value == color:
            parent[root(edge + 1)] = root(edge)
    labels = {}
    ids = []
    for vertex in range(len(parent)):
        representative = root(vertex)
        labels.setdefault(representative, len(labels))
        ids.append(labels[representative])
    return ids


def incidence_and_tree(bits):
    zero, one = color_components(bits, 0), color_components(bits, 1)
    nz, no = max(zero) + 1, max(one) + 1
    incidence = [[0] * no for _ in range(nz)]
    adjacency = [[0] * (nz+no) for _ in range(nz+no)]
    for i, j in zip(zero, one):
        incidence[i][j] += 1
        adjacency[i][nz+j] += 1
        adjacency[nz+j][i] += 1
    require(all(x in (0, 1) for row in incidence for x in row), "simple incidence")
    require(sum(map(sum, incidence)) == len(bits)+1, "tree edge count")
    reached, stack = set(), [0]
    while stack:
        node = stack.pop()
        if node not in reached:
            reached.add(node)
            stack.extend(i for i, value in enumerate(adjacency[node]) if value)
    require(len(reached) == len(adjacency) == len(bits)+2, "connected incidence tree")
    return incidence, adjacency, zero, one


def word_runs(bits):
    out = []
    start = 0
    for end in range(1, len(bits)+1):
        if end == len(bits) or bits[end] != bits[start]:
            out.append((start, end-start, bits[start]))
            start = end
    return out


def branch_moments(tree, hub, order=3):
    """Sum rooted 2j-step closed walks after deleting the marked hub."""
    roots = [i for i, entry in enumerate(tree[hub]) if entry]
    reduced = [row[:] for row in tree]
    for i in range(len(tree)):
        reduced[hub][i] = reduced[i][hub] = 0
    answers = [0] * order
    for root in roots:
        vector = [int(i == root) for i in range(len(tree))]
        for step in range(1, 2 * order + 1):
            vector = [sum(reduced[i][j] * vector[j] for j in range(len(tree)))
                      for i in range(len(tree))]
            if step % 2 == 0:
                answers[step//2-1] += vector[root]
    return answers


# Rational polynomials in ascending coefficient order. These routines do not
# use a symbolic algebra package and are independent of symbolic_checks.py.
def trim(p):
    p = list(map(Fraction, p))
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p or [Fraction(0)]


def padd(a, b):
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def pscale(p, c):
    return trim([x*c for x in p])


def pmul(a, b):
    p = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i+j] += x*y
    return trim(p)


def pdivmod(a, b):
    a, b = trim(a), trim(b)
    require(b != [0], "polynomial division by zero")
    q = [Fraction(0)] * max(1, len(a)-len(b)+1)
    while a != [0] and len(a) >= len(b):
        shift, ratio = len(a)-len(b), a[-1]/b[-1]
        q[shift] += ratio
        for j in range(len(b)):
            a[j+shift] -= ratio*b[j]
        a = trim(a)
    return trim(q), a


def pquot(a, b):
    q, r = pdivmod(a, b)
    require(r == [0], "nonexact polynomial quotient")
    return q


def pgcd(a, b):
    a, b = trim(a), trim(b)
    while b != [0]:
        a, b = b, pdivmod(a, b)[1]
    return pscale(a, 1/a[-1])


def derivative(p):
    return trim([i*p[i] for i in range(1, len(p))])


def monic_lcm(a, b):
    result = pquot(pmul(a, b), pgcd(a, b))
    return pscale(result, 1/result[-1])


def characteristic(a):
    """Newton trace identities: exact characteristic polynomial of an integer matrix."""
    n = len(a)
    power_sums = [0] + traces(a, n)
    descending = [Fraction(1)]
    for k in range(1, n+1):
        descending.append(-sum(descending[k-j]*power_sums[j]
                                for j in range(1, k+1))/k)
    require(all(x.denominator == 1 for x in descending), "integral characteristic")
    return trim(list(reversed(descending)))


def nonzero_characteristic(a):
    p = characteristic(a)
    while len(p) > 1 and p[0] == 0:
        p.pop(0)
    return p


def rational_add(n, d, a, b):
    n, d = padd(pmul(n, b), pmul(a, d)), pmul(d, b)
    g = pgcd(n, d)
    n, d = pquot(n, g), pquot(d, g)
    return pscale(n, 1/d[0]), pscale(d, 1/d[0])


def mtrim(p, prime):
    p = [int(x) % prime for x in p]
    while len(p)>1 and p[-1] == 0:
        p.pop()
    return p


def mmod(a, b, prime):
    a, b = mtrim(a, prime), mtrim(b, prime)
    require(b != [0], "modular zero divisor")
    while a != [0] and len(a) >= len(b):
        shift, ratio = len(a)-len(b), a[-1]*pow(b[-1], -1, prime) % prime
        for j in range(len(b)):
            a[j+shift] = (a[j+shift]-ratio*b[j]) % prime
        a = mtrim(a, prime)
    return a


def mgcd(a, b, prime):
    while b != [0]:
        a, b = b, mmod(a, b, prime)
    return mtrim([x*pow(a[-1], -1, prime) for x in a], prime)


def mpow(base, exponent, modulus, prime):
    result = [1]
    while exponent:
        if exponent & 1:
            result = mmod(pmul(result, base), modulus, prime)
        base = mmod(pmul(base, base), modulus, prime)
        exponent //= 2
    return result


def irreducible_mod(p, prime):
    p = mtrim(p, prime)
    degree = len(p)-1
    if degree < 1:
        return False
    xpower = [0, 1]
    # Rabin's criterion; testing every i <= degree//2 is redundant but simple.
    for i in range(1, degree+1):
        xpower = mpow(xpower, prime, p, prime)
        difference = mtrim(padd(xpower, [0, -1]), prime)
        if i <= degree//2 and len(mgcd(p, difference, prime)) > 1:
            return False
    return difference == [0]


def check_fixed_height(max_h, power_limit):
    results = []
    for h in range(1, max_h+1):
        expected = [Fraction(1)]
        numerator, denominator = [Fraction(0)], [Fraction(1)]
        char_cache = Counter()
        rank_sum = 0
        grams = []
        for bits in product((0, 1), repeat=h):
            c, _, _, _ = incidence_and_tree(bits)
            gram = matmul(c, transpose(c)) if len(c) <= len(c[0]) else matmul(transpose(c), c)
            grams.append(gram)
            require(len(gram) <= (h+2)//2, f"Gram degree bound h={h}")
            char = nonzero_characteristic(gram)
            rank_sum += len(char)-1
            opposite, _, _, _ = incidence_and_tree(tuple(1-b for b in bits))
            require(opposite == transpose(c), "complement transposes incidence")
            other = matmul(opposite, transpose(opposite)) if len(opposite) <= len(opposite[0]) else matmul(transpose(opposite), opposite)
            require(char == nonzero_characteristic(other), "complement spectral multiplicity")
            require(traces(gram, power_limit) == traces(binary_transition(bits), power_limit),
                    "smaller Gram trace identity")
            char_cache[tuple(char)] += 1
        for char_tuple, weight in sorted(char_cache.items()):
            require(weight > 0 and weight % 2 == 0, "even complement-paired spectral multiset")
            char = list(char_tuple)
            squarefree = pquot(char, pgcd(char, derivative(char)))
            expected = monic_lcm(expected, squarefree)
            q = trim(list(reversed(char)))
            term = [0] + [-weight*i*q[i] for i in range(1, len(q))]
            numerator, denominator = rational_add(numerator, denominator, term, q)
        expected_q = trim(list(reversed(expected)))
        expected_q = pscale(expected_q, 1/expected_q[0])
        require(denominator == expected_q, "GF minimal denominator has no cancellation")
        require(len(pgcd(denominator, derivative(denominator))) == 1,
                "fixed-height denominator squarefree")
        require(all(x.denominator == 1 for x in denominator+numerator), "integral GF")
        require(all(int(x) % 2 == 0 for x in numerator), "GF complement-pair parity")
        series_limit = len(denominator)+2
        direct = [0] * series_limit
        for gram in grams:
            direct = [a+b for a, b in zip(direct, traces(gram, series_limit))]
        series = [Fraction(0)]
        for power in range(1, series_limit+1):
            coefficient = numerator[power] if power < len(numerator) else 0
            coefficient -= sum(denominator[j]*series[power-j]
                               for j in range(1, min(power, len(denominator)-1)+1))
            series.append(coefficient)
        require(series[1:] == direct, "reduced GF coefficients match independent matrix powers")
        results.append({"h": h, "gram_degree_bound": (h+2)//2,
                        "minimal_recurrence_order": len(denominator)-1,
                        "generating_function_coefficients_checked": series_limit,
                        "positive_spectral_multiplicity": rank_sum,
                        "denominator_ascending": list(map(int, denominator)),
                        "numerator_ascending": list(map(int, numerator))})
    return results


def check_prime_sharpness(extended=False):
    out = []
    for prime in ((5, 7, 11, 13, 17, 19) if extended else (5, 7, 11)):
        h = prime-3
        c, tree, _, _ = incidence_and_tree(tuple(i % 2 for i in range(h)))
        degrees = list(map(sum, tree))
        require(degrees.count(1) == 2 and all(d in (1, 2) for d in degrees), "alternating path")
        gram = matmul(c, transpose(c)) if len(c) <= len(c[0]) else matmul(transpose(c), c)
        char = characteristic(gram)
        require(len(char)-1 == (prime-1)//2 == (h+2)//2, "sharp path degree")
        witnesses = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)
        witness = next((ell for ell in witnesses if irreducible_mod(char, ell)), None)
        require(witness is not None, f"missing irreducibility witness p={prime}")
        out.append({"prime": prime, "height_h": h, "degree": len(char)-1,
                    "irreducible_mod_prime": witness, "characteristic_ascending": list(map(int, char))})
    return out


def run_exact_checks(extended=False):
    rectangle_limit = 7 if extended else 6
    word_limit = 9 if extended else 7
    identity_power = 4
    geometry, stats = {}, []
    for w in range(1, rectangle_limit+1):
        geometry[w], stat = geometric_counts(rectangle_limit, w)
        stats.append(stat)
    table, brute_cases = [], 0
    words_checked, marks_checked = 0, 0
    multiplicities = []
    for h in range(1, word_limit+1):
        trace_totals = [0] * rectangle_limit
        marks, moment_sum = Counter(), Counter()
        for bits in product((0, 1), repeat=h):
            words_checked += 1
            transition = binary_transition(bits)
            if h <= rectangle_limit:
                trace_totals = [a+b for a, b in zip(trace_totals, traces(transition, rectangle_limit))]
            c, tree, zero, one = incidence_and_tree(bits)
            e0 = [[int(i == j) for j in zero] for i in zero]
            e1 = [[int(i == j) for j in one] for i in one]
            require(transition == matmul(e0, e1), f"E0E1 h={h} bits={bits}")
            gram = matmul(c, transpose(c))
            mt, gt, tt = traces(transition, identity_power), traces(gram, identity_power), traces(tree, 2*identity_power)
            require(mt == gt == [tt[2*j+1]//2 for j in range(identity_power)], "tree/Gram trace identity")
            require(all(tt[2*j+1] % 2 == 0 for j in range(identity_power)), "tree trace parity")
            runs = word_runs(bits)
            for r, (start, size, color) in enumerate(runs):
                marks_checked += 1
                hub = zero[start] if color == 0 else len(c)+one[start]
                require(sum(tree[hub]) == size+1, "run hub degree")
                actual = branch_moments(tree, hub)
                left = runs[r-1][1] if r else 0
                right = runs[r+1][1] if r+1 < len(runs) else 0
                next_left = runs[r-2][1] if r >= 2 else 0
                next_right = runs[r+2][1] if r+2 < len(runs) else 0
                require(actual[0] == left+right, "first rooted branch moment")
                require(actual[1] == left*left+right*right+next_left+next_right,
                        "second rooted branch moment")
                defect = h-size
                require(all(0 <= moment <= actual[0]*defect**j
                            for j, moment in enumerate(actual)), "integer rooted moment bound")
                marks[size] += 1
                moment_sum[size] += actual[0]
        for size in range(1, h+1):
            k = h-size
            expected = 2 if k == 0 else (k+3)*2**(k-1)
            expected_moment = 0 if k == 0 else 4*k*2**(k-1)
            require(marks[size] == expected, "marked-run multiplicity")
            require(moment_sum[size] == expected_moment, "marked B1 sum")
            multiplicities.append({"h": h, "run_length": size, "marked_words": expected,
                                   "B1_sum": expected_moment})
        if h <= rectangle_limit:
            for w in range(1, rectangle_limit+1):
                maximum, count = geometry[w][h]
                require(maximum == h*w, "geometric maximum density")
                require(count == trace_totals[w-1], f"independent counts h={h} w={w}")
                brute = subset_count(h, w) if h*w <= (6 if extended else 5) else None
                if brute is not None:
                    require(brute == count, "brute subset comparison")
                    brute_cases += 1
                table.append({"h": h, "w": w, "maximum_kings": maximum,
                              "geometric_count": count, "binary_trace_count": trace_totals[w-1],
                              "brute_subset_count": brute})
    for h in range(1, rectangle_limit+1):
        require(geometry[1][h][1] == (h+1)*2**h, "w=1 formula")
        require(geometry[2][h][1] == (5*h-3)*2**h+4, "w=2 formula")
    older, current = 2, 3
    for w in range(1, rectangle_limit+1):
        if w > 1:
            older, current = current, 3*current-older
        require(geometry[w][1][1] == 2**(w+1), "h=1 formula")
        require(geometry[w][2][1] == 2*(3**w+current), "h=2 formula")
    return {"scope": "exact finite checks; these computations are not asymptotic proofs",
            "rectangle_limit": rectangle_limit, "word_identity_height_limit": word_limit,
            "trace_power_limit": identity_power, "words_checked": words_checked,
            "marked_runs_checked": marks_checked, "brute_cases": brute_cases,
            "row_mask_statistics": stats, "exact_rectangles": table,
            "marked_run_moments": multiplicities,
            "fixed_height_structure": check_fixed_height(6 if extended else 5, 3),
            "alternating_prime_sharpness": check_prime_sharpness(extended)}
