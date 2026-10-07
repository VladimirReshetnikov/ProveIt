"""Exact finite computations for Report 227; Python standard library only.

All indices start at zero, and arrays include the requested final index.
The public test suite uses require(), never removable Python assertions.
"""
from collections import Counter
from functools import lru_cache
from math import comb, gamma, sqrt, pi, log, exp

MAX_COEFFICIENT = 1000
MAX_BOUNDED_N = 96
MAX_DEGREE = 32
MAX_ORBIT_N = 12


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def cap(value, low, high, name):
    require(isinstance(value, int) and not isinstance(value, bool)
            and low <= value <= high,
            f"{name} must be an integer in [{low}, {high}]")


def quotient(numerator, denominator, label):
    q, r = divmod(numerator, denominator)
    require(r == 0, f"nonintegral {label}: remainder {r}")
    return q


def convolution(a, b, n=None):
    if n is None:
        n = min(len(a), len(b)) - 1
    out = [0] * (n + 1)
    for i, x in enumerate(a[:n + 1]):
        if x:
            for j, y in enumerate(b[:n + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def product(n, *factors):
    out = [1] + [0] * n
    for factor in factors:
        out = convolution(out, factor, n)
    return out


def shifted(a, shift, n=None):
    if n is None:
        n = len(a) - 1
    return ([0] * shift + list(a))[:n + 1]


def dilated(a, factor, n=None):
    if n is None:
        n = len(a) - 1
    return [a[j // factor] if j % factor == 0 else 0 for j in range(n + 1)]


def rooted_coefficients(n):
    """Otter/Pólya logarithmic recurrence, independent of bounded DP below."""
    cap(n, 1, MAX_COEFFICIENT + 2, "rooted final index")
    r, sigma = [0] * (n + 1), [0] * (n + 1)
    r[1] = 1
    for size in range(1, n + 1):
        if size > 1:
            r[size] = quotient(sum(sigma[j] * r[size - j]
                                   for j in range(1, size)), size - 1,
                               "rooted recurrence")
        for multiple in range(size, n + 1, size):
            sigma[multiple] += size * r[size]
    return r


def euler_product(exponents, n):
    """Coefficients of product_(j>=1) (1-z^j)^(-exponents[j])."""
    require(len(exponents) > n, "Euler exponents do not reach final index")
    divisor_sum = [0] * (n + 1)
    for j in range(1, n + 1):
        require(exponents[j] >= 0, "negative Euler exponent")
        for multiple in range(j, n + 1, j):
            divisor_sum[multiple] += j * exponents[j]
    out = [1] + [0] * n
    for m in range(1, n + 1):
        out[m] = quotient(sum(divisor_sum[j] * out[m - j]
                              for j in range(1, m + 1)), m, "Euler recurrence")
    return out


def direct_euler_product(exponents, n):
    """Independent multiplication of binomial factors, for finite cross-checks."""
    out = [1] + [0] * n
    for weight in range(1, n + 1):
        multiplicity = exponents[weight]
        if not multiplicity:
            continue
        factor = [0] * (n + 1)
        for copies in range(n // weight + 1):
            factor[copies * weight] = comb(multiplicity + copies - 1, copies)
        out = convolution(out, factor, n)
    return out


def sequences(r, n):
    g = [1] + [0] * n
    for m in range(1, n + 1):
        g[m] = sum(r[j] * g[m - j] for j in range(1, m + 1))
    return g


def basic_series(n):
    cap(n, 1, MAX_COEFFICIENT, "series final index")
    r = rooted_coefficients(n + 2)
    h = euler_product([0] + r[2:n + 2], n)
    j2 = euler_product([0] + r[3:n + 3], n)
    g = sequences(r, n)
    f = convolution(h, g, n)
    return {"r": r, "H": h, "J2": j2, "G": g, "F": f}


def defect_series(series, n=None):
    """Both the positive and signed definitions of B(z)=sum b_r z^r."""
    if n is None:
        n = len(series["F"]) - 1
    r, h, j2, g, f = (series[key][:n + 1]
                       for key in ("r", "H", "J2", "G", "F"))
    geom, one_plus_z = [1] * (n + 1), [1, 1] + [0] * (n - 1)
    f_squared = convolution(f, f, n)
    f_z2 = dilated(f, 2, n)
    distinct = [quotient(a - b, 2, "distinct-pair coefficient")
                for a, b in zip(f_squared, f_z2)]
    require(all(x >= 0 for x in distinct), "negative distinct-pair count")
    truncation = shifted(product(n, j2, g, geom), 1, n)
    ordinary = product(n, one_plus_z, f_squared, geom)
    extra = shifted(product(n, f_squared, geom), 1, n)
    inside = [a + b for a, b in zip(distinct, extra)]
    branch_positive = shifted(product(n, r, g, inside), 1, n)
    b = [a + c + d for a, c, d in zip(truncation, ordinary, branch_positive)]
    branch_twice = shifted(product(n, one_plus_z, r, h, h, g, g, g, geom), 1, n)
    symmetric = shifted(product(n, r, g, f_z2), 1, n)
    signed = [quotient(2 * a + 2 * c + d - e, 2, "signed defect")
              for a, c, d, e in zip(truncation, ordinary, branch_twice, symmetric)]
    require(b == signed, "positive and signed defect series disagree")
    require(all(x > 0 for x in b), "nonpositive defect coefficient")
    return {"B": b, "truncation": truncation, "symmetric_residual": symmetric}


def component_forests(exponents, n):
    """Independent [v^j z^m] product (1-v z^s)^(-a_s), triangular DP."""
    cap(n, 1, MAX_BOUNDED_N, "component-forest final index")
    table = [[0] * (n + 1) for _ in range(n + 1)]
    table[0][0] = 1
    for weight in range(1, n + 1):
        multiplicity = exponents[weight]
        if not multiplicity:
            continue
        previous = table
        table = [row[:] for row in previous]
        for copies in range(1, n // weight + 1):
            shift = copies * weight
            ways = comb(multiplicity + copies - 1, copies)
            for parts in range(n - copies + 1):
                for degree in range(parts, n - shift + 1):
                    count = previous[parts][degree]
                    if count:
                        table[parts + copies][degree + shift] += count * ways
    return table


def bounded_trees(n, degree_cap):
    """Trees with all outdegrees <= degree_cap, via size-ordered multiset DP.

    This routine never uses r_n, H, F or B. After forest factors of child
    sizes below s have been included, the coefficient of z^(s-1) gives the
    number of allowed size-s child types. Its new binomial factor is then
    included. A second variable records and bounds the root's child count.
    """
    cap(n, 1, MAX_BOUNDED_N, "bounded-tree final index")
    cap(degree_cap, 0, MAX_DEGREE, "outdegree cap")
    forest = [[0] * n for _ in range(degree_cap + 1)]
    forest[0][0] = 1
    trees = [0] * (n + 1)
    for size in range(1, n + 1):
        trees[size] = sum(forest[j][size - 1] for j in range(degree_cap + 1))
        multiplicity = trees[size]
        if not multiplicity or size == n:
            continue
        previous = forest
        forest = [row[:] for row in previous]
        for copies in range(1, min(degree_cap, (n - 1) // size) + 1):
            ways = comb(multiplicity + copies - 1, copies)
            shift = copies * size
            for parts in range(degree_cap - copies + 1):
                for total in range(n - shift):
                    if previous[parts][total]:
                        forest[parts + copies][total + shift] += ways * previous[parts][total]
    return trees


def bounded_checks(n, degree_cap, series, defect):
    cap(degree_cap, 1, min(MAX_DEGREE, n - 1), "tested maximum degree")
    table = component_forests([0] + series["r"][2:n + 2], n)
    h = [sum(row[m] for row in table) for m in range(n + 1)]
    require(h == series["H"][:n + 1], "component DP disagrees with H Euler recurrence")
    j_direct = direct_euler_product([0] + series["r"][3:n + 3], n)
    require(j_direct == series["J2"][:n + 1], "direct factors disagree with J2 recurrence")
    all_counts = {0: bounded_trees(n, 0)}
    counts = Counter()
    for k in range(1, degree_cap + 1):
        all_counts[k] = bounded_trees(n, k)
        hk = [sum(table[j][m] for j in range(k + 1)) for m in range(n + 1)]
        pointed = convolution(hk, series["G"], n)
        for size in range(1, n + 1):
            actual = all_counts[k][size] - all_counts[k - 1][size]
            require(actual >= 0, f"negative maximum-exact count N={size}, k={k}")
            if k >= size - 1:
                require(all_counts[k][size] == series["r"][size], "bounded counts do not recover r_n")
                counts["unrestricted_recovery"] += 1
            if size < k + 1:
                require(actual == 0, "impossible maximum has nonzero count")
                continue
            m = size - k - 1
            require(actual <= pointed[m] <= series["F"][m], "pointing/truncation inequality failed")
            counts["pointing_inequality"] += 1
            if size <= 2 * k:
                require(actual == series["F"][m], f"plateau N={size}, k={k}")
                counts["plateau"] += 1
            if size == 2 * k + 1:
                require(actual == series["F"][m] - 1, f"first boundary k={k}")
                counts["first_boundary"] += 1
            residual = size - 2 * k - 1
            if 0 <= residual < k:
                require(actual == series["F"][m] - defect["B"][residual], f"two-hub N={size}, k={k}")
                counts["two_hub"] += 1
            if 0 <= residual <= k:
                require(series["F"][m] - pointed[m] == defect["truncation"][residual], f"forest truncation N={size}, k={k}")
                counts["forest_truncation"] += 1
            if size == 3 * k + 1:
                require(actual == series["F"][2 * k] - defect["B"][k] + 2, f"third boundary k={k}")
                counts["third_boundary"] += 1
    return dict(counts), all_counts, table


@lru_cache(maxsize=None)
def canonical_trees(n):
    """Unlabeled nonplane rooted trees, represented as sorted nested tuples."""
    cap(n, 1, MAX_ORBIT_N, "canonical size")
    if n == 1:
        return ((),)
    choices = sorted((size, tree) for size in range(1, n)
                     for tree in canonical_trees(size))
    output = []
    def choose(remaining, lower, children):
        if remaining == 0:
            output.append(tuple(sorted(children)))
            return
        for index in range(lower, len(choices)):
            size, tree = choices[index]
            if size > remaining:
                break
            choose(remaining - size, index, children + (tree,))
    choose(n - 1, 0, ())
    require(len(output) == len(set(output)), "canonical generator emitted duplicates")
    return tuple(output)


def vertices(tree, path=()):
    yield path, tree
    for index, child in enumerate(tree):
        yield from vertices(child, path + (index,))


def colored_form(tree, marks, path=()):
    """Canonical colored rooted tree; no raw-vertex/orbit identification."""
    return (marks.get(path, 0), tuple(sorted(
        colored_form(child, marks, path + (index,))
        for index, child in enumerate(tree))))


def orbit_checks(n, series, defect, bounded, forest_table):
    cap(n, 1, MAX_ORBIT_N, "colored-orbit final size")
    r, g, f = (series[key][:n + 1] for key in ("r", "G", "F"))
    one, pairs, maxima, symmetric = Counter(), Counter(), Counter(), Counter()
    total_types = 0
    for size in range(1, n + 1):
        trees = canonical_trees(size)
        require(len(trees) == r[size], f"canonical tree count at N={size}")
        total_types += len(trees)
        for tree in trees:
            vs = list(vertices(tree))
            degrees = {path: len(branch) for path, branch in vs}
            maxima[size, max(degrees.values())] += 1
            single = {path: colored_form(tree, {path: 1}) for path, _ in vs}
            canonical_one = {form: (degrees[path], len(path)) for path, form in single.items()}
            for degree, depth in canonical_one.values():
                one[size, degree, depth] += 1
            canonical_pairs = {}
            for left, _ in vs:
                for right, _ in vs:
                    if left != right:
                        canonical_pairs[colored_form(tree, {left: 1, right: 2})] = (degrees[left], degrees[right])
            for degrees_pair in canonical_pairs.values():
                pairs[size, *degrees_pair] += 1
            # Actual same-single-orbit pair types in the supported sector.
            for k in range(1, size):
                if 0 <= size - 2 * k - 1 <= k:
                    high = [path for path in degrees if degrees[path] >= k]
                    candidates = [path for path in high if degrees[path] == k]
                    same = any(single[p] == single[q] for i, p in enumerate(candidates)
                               for q in candidates[i + 1:])
                    symmetric[size, k] += int(same)
    counts = Counter()
    powers = [[1] + [0] * n]
    for depth in range(1, n + 1):
        powers.append(convolution(powers[-1], r, n))
    hk = [[sum(forest_table[j][m] for j in range(k + 1)) for m in range(n + 1)]
          for k in range(n)]
    for k in range(n):
        for depth in range(n):
            expected = convolution(hk[k], powers[depth], n)
            for size in range(k + 1, n + 1):
                require(one[size, k, depth] == expected[size - k - 1],
                        f"one-color/depth identity N={size}, k={k}, depth={depth}")
                counts["one_color_depth"] += 1
    g2, g3 = product(n, g, g), product(n, g, g, g)
    # Q_(d,e)=G^2(B_d M_e+M_d B_e)+R G^3 M_d M_e.
    mseries = [shifted(hk[d], d + 1, n) for d in range(n)]
    bseries = [[0] * (n + 1)] + [shifted(hk[d - 1], d, n) for d in range(1, n)]
    for d in range(n):
        for e in range(n):
            first = product(n, bseries[d], mseries[e], g2)
            second = product(n, mseries[d], bseries[e], g2)
            third = product(n, r, mseries[d], mseries[e], g3)
            for size in range(1, n + 1):
                require(pairs[size, d, e] == first[size] + second[size] + third[size],
                        f"two-color identity N={size}, d={d}, e={e}")
                counts["two_color_degree_pair"] += 1
    # An additional coefficientwise majorant used by the uniform-error proof.
    # Check it against explicitly colored orbits, rather than raw vertex pairs.
    h = series["H"][:n + 1]
    geom = [1] * (n + 1)
    ancestor_bound = product(n, h, h, g2, geom, geom)
    branch_bound = product(n, r, h, h, g3, geom, geom)
    for k in range(1, n):
        left = shifted(ancestor_bound, 2 * k + 1, n)
        right = shifted(branch_bound, 2 * k + 2, n)
        for size in range(1, n + 1):
            pair_count = sum(pairs[size, d, e] for d in range(k, n) for e in range(k, n))
            require(pair_count <= 2 * left[size] + right[size], "pair-orbit coefficientwise majorant")
            counts["pair_coefficientwise_majorant"] += 1
    for size in range(1, n + 1):
        for k in range(size):
            independent = bounded[k][size] - (bounded[k - 1][size] if k else 0)
            require(maxima[size, k] == independent, "canonical maxima disagree with bounded DP")
            counts["canonical_maximum"] += 1
            if k == 0:
                continue
            p = sum(one[size, k, d] for d in range(size))
            q_ge = sum(pairs[size, d, e] for d in range(k, size) for e in range(k, size))
            require(0 <= p - maxima[size, k] <= q_ge, "pointing-surplus ordered-pair bound")
            counts["orbit_surplus_bound"] += 1
            residual = size - 2 * k - 1
            if 0 <= residual <= k:
                qkk = pairs[size, k, k]
                qkg = sum(pairs[size, k, e] for e in range(k + 1, size))
                s = symmetric[size, k]
                require(s == defect["symmetric_residual"][residual], "symmetric-pair residual formula")
                boundary_extra = int(residual == k)
                require(2 * maxima[size, k] == 2 * p - qkk + s - 2 * qkg + 2 * boundary_extra,
                        "quadratic orbit correction failed")
                counts["symmetric_and_sector_orbits"] += 1
    return {"tree_types_total": total_types, "tree_types_at_final_size": r[n], **dict(counts)}


def falling(value, order):
    result = 1
    for i in range(order):
        result *= value - i
    return result


def moment_diagnostics(series, final_index, maximum_order=4):
    """Exact numerators, plus non-certified float comparisons with limit scales."""
    cap(final_index, 1, MAX_COEFFICIENT, "moment final index")
    cap(maximum_order, 1, 6, "moment order")
    r, h, g, f = (series[key][:final_index + 1] for key in ("r", "H", "G", "F"))
    require(all(f[m] > f[m - 1] for m in range(1, final_index + 1)), "f_m is not increasing")
    falling_moments = [f]
    for order in range(1, maximum_order + 1):
        current = [0] * (final_index + 1)
        for m in range(1, final_index + 1):
            current[m] = sum(r[j] * (current[m - j] + order * falling_moments[-1][m - j])
                             for j in range(1, m + 1))
        falling_moments.append(current)
    # A separate finite sum over spine lengths checks each exact moment.
    small = min(16, final_index)
    direct = [[0] * (small + 1) for _ in range(maximum_order + 1)]
    rpower = [1] + [0] * small
    for depth in range(small + 1):
        objects = convolution(h, rpower, small)
        for order in range(maximum_order + 1):
            for m in range(small + 1):
                direct[order][m] += falling(depth, order) * objects[m]
        rpower = convolution(rpower, r, small)
    for order in range(maximum_order + 1):
        require(direct[order] == falling_moments[order][:small + 1], "direct depth moments disagree")
    rho = 0.33832185689920769519611262571701705318
    beta = 1.5594900203746408855422073958948854144
    samples = sorted(set([max(1, final_index // 8), max(1, final_index // 2), final_index]))
    depth_output, decoration_output = {}, {}
    for order in range(1, maximum_order + 1):
        depth_scale = (2 / beta) ** order * gamma(1 + order / 2)
        deco_scale = beta * gamma(order - .5) / (2 * rho * gamma(order))
        depth_output[str(order)], decoration_output[str(order)] = [], []
        for m in samples:
            depth_ratio = (falling_moments[order][m] / f[m]) / (m ** (order / 2) * depth_scale)
            decoration_numerator = sum(j ** order * h[j] * g[m - j] for j in range(m + 1))
            deco_ratio = (decoration_numerator / f[m]) / (m ** (order - .5) * deco_scale)
            depth_output[str(order)].append({"m": m, "ratio_to_leading_equivalent": depth_ratio})
            decoration_output[str(order)].append({"m": m, "ratio_to_leading_equivalent": deco_ratio})
    return {"warning": "Exact integer numerators; float ratios use uncertified constants and are diagnostics, not limit proofs.",
            "moment_orders": maximum_order, "exact_direct_crosschecks": (maximum_order + 1) * (small + 1),
            "depth_falling_moments": depth_output, "decoration_integer_moments": decoration_output}


def defect_diagnostics(defect, final_index):
    """Compare exact b_r with its leading scale, using logs to avoid overflow."""
    cap(final_index, 1, MAX_COEFFICIENT, "defect final index")
    require(len(defect["B"]) > final_index, "defect series is shorter than diagnostics")
    rho = 0.33832185689920769519611262571701705318
    beta = 1.5594900203746408855422073958948854144
    c = 7.7581602911970581270533094315220363519
    leading = rho * (1 + rho) * c ** 2 / ((1 - rho) * beta ** 3 * sqrt(pi))
    k = c / (beta * sqrt(pi))
    samples = sorted(set([max(1, final_index // 8), max(1, final_index // 2), final_index]))
    ratios = []
    for r in samples:
        exact = defect["B"][r]
        ratio = exp(log(exact) + r * log(rho) - .5 * log(r) - log(leading))
        ratios.append({"r": r, "exact_b_r": exact, "ratio_to_leading_equivalent": ratio,
                       "r_times_ratio_minus_one": r * (ratio - 1)})
    return {"warning": "Exact coefficients; logarithmic float comparisons and leading constants are uncertified diagnostics.",
            "coefficient_final_index": final_index, "L": leading, "L_over_K": leading / k,
            "samples": ratios}
