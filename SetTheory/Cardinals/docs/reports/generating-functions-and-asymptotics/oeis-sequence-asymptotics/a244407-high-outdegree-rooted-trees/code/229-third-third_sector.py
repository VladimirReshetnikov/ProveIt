"""Exact finite verification for the third high-degree sector of rooted trees.

All coefficients are integers. Universal Euler products and the independent
bounded-tree cycle-index recurrence are deliberately separate constructions.
No assertion is used for a mathematical, input, or resource check.
"""
from math import comb

MAX_N = 256
MAX_K = 80
MAX_ROOTED_N = 512
MAX_LITERAL_N = 12


def integer_range(name, value, lower, upper):
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{name} must be an integer")
    if not lower <= value <= upper:
        raise ValueError(f"{name} must be in [{lower}, {upper}]")
    return value


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def add(*series):
    if not series or not series[0] or any(len(a) != len(series[0]) for a in series):
        raise ValueError("add requires nonempty, equal-length coefficient arrays")
    return [sum(values) for values in zip(*series)]


def scale(a, multiplier):
    return [multiplier * x for x in a]


def mul(a, b):
    if not a or len(a) != len(b):
        raise ValueError("mul requires nonempty, equal-length coefficient arrays")
    result = [0] * len(a)
    nonzero_b = [(j, x) for j, x in enumerate(b) if x]
    for i, x in enumerate(a):
        if x:
            for j, y in nonzero_b:
                if i + j >= len(a):
                    break
                result[i + j] += x * y
    return result


def times(*series):
    if not series or not series[0]:
        raise ValueError("times requires at least one nonempty coefficient array")
    result = [1] + [0] * (len(series[0]) - 1)
    for a in series:
        result = mul(result, a)
    return result


def shift(a, amount):
    integer_range("shift", amount, 0, 10 * MAX_ROOTED_N)
    if not a:
        raise ValueError("shift requires a nonempty coefficient array")
    if amount >= len(a):
        return [0] * len(a)
    return [0] * amount + a[:len(a) - amount] if amount else list(a)


def substitute(a, degree):
    integer_range("substitution degree", degree, 1, MAX_ROOTED_N)
    return [a[m // degree] if m % degree == 0 else 0 for m in range(len(a))]


def divide_exact(a, divisor):
    integer_range("divisor", divisor, 1, MAX_ROOTED_N)
    require(all(x % divisor == 0 for x in a), "nonintegral coefficient division")
    return [x // divisor for x in a]


def geometric(n, degree=1):
    integer_range("series degree", n, 0, MAX_ROOTED_N)
    integer_range("geometric step", degree, 1, MAX_ROOTED_N)
    return [int(m % degree == 0) for m in range(n + 1)]


def rooted_counts(n):
    """r[0..n], by triangular successive binomial Euler-product factors."""
    integer_range("rooted count cutoff", n, 0, MAX_ROOTED_N)
    r = [0] * (n + 1)
    if not n:
        return r
    forest = [1] + [0] * (n - 1)
    for s in range(1, n + 1):
        r[s] = forest[s - 1]
        if s < n:
            factor = [0] * n
            for q in range((n - 1) // s + 1):
                factor[q * s] = comb(r[s] + q - 1, q)
            forest = mul(forest, factor)
    return r


def euler_product(exponents, n):
    """Product (1-z^s)^(-exponents[s]), truncated through degree n."""
    integer_range("Euler-product cutoff", n, 0, MAX_N)
    if len(exponents) != n + 1 or exponents[0] != 0:
        raise ValueError("Euler exponents must have length n+1 and zero constant")
    if any(isinstance(x, bool) or not isinstance(x, int) or x < 0 for x in exponents):
        raise ValueError("Euler exponents must be nonnegative integers")
    out = [1] + [0] * n
    for s in range(1, n + 1):
        multiplicity = exponents[s]
        if not multiplicity:
            continue
        factor = [0] * (n + 1)
        for q in range(n // s + 1):
            factor[q * s] = comb(multiplicity + q - 1, q)
        out = mul(out, factor)
    return out


def bounded_counts(n, k):
    """Trees of size <= n with maximum outdegree <= k.

    For each tree size, use d Z_d = sum_(j=1)^d A(z^j) Z_(d-j).
    Coefficients A_s needed on the right have already been computed. This is
    a cycle-index construction, not the Euler-product construction above.
    """
    integer_range("N", n, 1, MAX_N)
    integer_range("k", k, 0, MAX_K)
    a = [0] * (n + 1)
    a[1] = 1
    forest = [[0] * (k + 1) for _ in range(n)]
    forest[0][0] = 1
    for m in range(1, n):
        for d in range(1, min(k, m) + 1):
            numerator = 0
            for j in range(1, min(d, m) + 1):
                for s in range(1, m // j + 1):
                    numerator += a[s] * forest[m - j * s][d - j]
            require(numerator % d == 0, f"cycle-index division failed at {(m, d, k)}")
            forest[m][d] = numerator // d
        a[m + 1] = sum(forest[m])
    return a


def universal_series(n):
    """Return R,H,J2,J3,G,F,B,a,D,c,U,V,W and all-size deficit layers.

    B is formed from its original positive expression, independently of the
    later identity B=(1-z^2)G(aD+zc+zR E2(D)).
    """
    integer_range("N", n, 1, MAX_N)
    rr = rooted_counts(n + 3)
    R = rr[:n + 1]
    H = euler_product([0] + rr[2:n + 2], n)
    J2 = euler_product([0] + rr[3:n + 3], n)
    J3 = euler_product([0] + rr[4:n + 4], n)
    G = [1] + [0] * n
    for m in range(1, n + 1):
        G[m] = sum(R[q] * G[m - q] for q in range(1, m + 1))
    F = mul(H, G)
    g1, g2, g3 = geometric(n), geometric(n, 2), geometric(n, 3)
    a, D, c = mul(H, g1), times(G, H, g1), times(J2, g1, g2)
    E2F = divide_exact(add(mul(F, F), scale(substitute(F, 2), -1)), 2)
    B = add(shift(times(J2, G, g1), 1),
            times(add(F, shift(F, 1)), F, g1),
            shift(times(R, G, add(E2F, shift(times(F, F, g1), 1))), 1))
    E2D = divide_exact(add(mul(D, D), scale(substitute(D, 2), -1)), 2)
    E3D = divide_exact(add(times(D, D, D), scale(mul(D, substitute(D, 2)), -3),
                          scale(substitute(D, 3), 2)), 6)
    marked = [0] * (n + 1)
    for weight in range(1, n + 1):
        for m in range(weight, n + 1, weight):
            marked[m] += rr[weight + 3]
    J3v = mul(J3, marked)
    V = shift(times(G, J3, g1, g2), 3)
    W = shift(times(G, g1, g2, add(J3, mul(J3, g1), mul(J3, g2), scale(J3v, -1))), 3)
    Y = mul(G, add(mul(c, D), times(add(a, shift(mul(R, D), 1)), B, g2),
                   mul(a, E2D), shift(mul(R, E3D), 2)))
    U = add(W, Y, scale(shift(Y, 3), -1))
    # Deficit layers are also built directly, rather than inverted from U,V.
    L = times(J3, g1, g2, g3)
    Q = times(g1, g2, g3,
              add(mul(J3, add(scale([1] + [0] * n, 3), shift(g1, 1),
                              shift(g2, 2), shift(g3, 3))), scale(J3v, -1)))
    P = mul(B, g2)
    K = shift(mul(G, L), 3)
    H0 = add(shift(mul(G, Q), 3), Y)
    B_alt = add(times(G, a, D), shift(times(G, c), 1), shift(times(G, R, E2D), 1))
    require(B == add(B_alt, scale(shift(B_alt, 2), -1)), "positive-B identity failed")
    require(V == add(K, scale(shift(K, 3), -1)), "V deficit identity failed")
    require(U == add(H0, scale(shift(H0, 3), -1), scale(shift(K, 3), -1)),
            "U deficit identity failed")
    return {name: value for name, value in locals().items() if name in
            ("R", "H", "J2", "J3", "J3v", "G", "F", "B", "a", "D", "c",
             "E2D", "E3D", "U", "V", "W", "P", "L", "Q", "K", "H0")}


def check_exact(n=192, kmax=64):
    integer_range("N", n, 1, MAX_N)
    integer_range("k_max", kmax, 1, MAX_K)
    series = universal_series(n)
    previous = bounded_counts(n, 0)
    sector_cases, deficit_cases, boundaries, last_counts = 0, 0, [], []
    for k in range(1, kmax + 1):
        current = bounded_counts(n, k)
        for r in range(k):
            size = 3 * k + r + 1
            if size > n:
                break
            actual = current[size] - previous[size]
            expected = (series['F'][2 * k + r] - series['B'][k + r]
                        + series['U'][r] + k * series['V'][r])
            require(actual == expected, f"third-sector mismatch at N={size}, k={k}, r={r}")
            sector_cases += 1
        predicted = add(shift(series['D'], k + 1), scale(shift(series['P'], 2 * k + 1), -1),
                        shift(add(series['H0'], scale(series['K'], k)), 3 * k + 1))
        for size in range(min(n, 4 * k) + 1):
            actual = series['R'][size] - previous[size]
            require(predicted[size] == actual, f"all-size deficit mismatch at N={size}, k={k}")
            deficit_cases += 1
        size = 4 * k + 1
        if size <= n:
            residual = current[size] - previous[size] - (series['F'][3 * k] - series['B'][2 * k]
                                                       + series['U'][k] + k * series['V'][k])
            require(residual == (-6 if k == 1 else -7), f"next-boundary mismatch at k={k}")
            boundaries.append({'k': k, 'residual': residual})
        last_counts.append([k, current[n]])
        previous = current
    first_negative = next(([i, x] for i, x in enumerate(series['W']) if x < 0), None)
    require(series['U'][:min(10, n + 1)] == [2,20,120,602,2674,11069,43479,164468,603971,2166927][:n + 1],
            "U initial-coefficient integrity check failed")
    require(series['V'][:min(10, n + 1)] == [0,0,0,1,6,32,145,616,2464,9498][:n + 1],
            "V initial-coefficient integrity check failed")
    if n >= 13:
        require(first_negative == [13, -7692], "W first-negative integrity check failed")
    return {'status': 'pass', 'N': n, 'k_max': kmax, 'third_sector_cases': sector_cases,
            'all_size_deficit_cases': deficit_cases, 'boundary_checks': boundaries,
            'U_first_31': series['U'][:31], 'V_first_31': series['V'][:31],
            'W_first_negative': first_negative, 'bounded_counts_at_N': last_counts}


def root_forest_cycle(rooted, n):
    """[weight][component count] for unrestricted root forests via cycle indices."""
    integer_range("forest cutoff", n, 1, MAX_N)
    if len(rooted) < n + 1 or rooted[0] != 0:
        raise ValueError("rooted coefficients must include degrees 0 through n and have zero constant")
    forest = [[0] * (n + 1) for _ in range(n + 1)]
    forest[0][0] = 1
    for m in range(1, n + 1):
        for d in range(1, m + 1):
            numerator = sum(rooted[s] * forest[m - j * s][d - j]
                            for j in range(1, d + 1) for s in range(1, m // j + 1))
            require(numerator % d == 0, f"root forest division failed at {(m, d)}")
            forest[m][d] = numerator // d
    return forest


def marked_euler_product(exponents, n):
    """[weight][components] of product (1-v z^s)^(-exponents[s])."""
    integer_range("marked Euler-product cutoff", n, 1, MAX_N)
    if len(exponents) != n + 1 or exponents[0] != 0:
        raise ValueError("marked Euler exponents must have length n+1 and zero constant")
    if any(isinstance(x, bool) or not isinstance(x, int) or x < 0 for x in exponents):
        raise ValueError("marked Euler exponents must be nonnegative integers")
    out = [[0] * (n + 1) for _ in range(n + 1)]
    out[0][0] = 1
    for s in range(1, n + 1):
        count = exponents[s]
        if not count:
            continue
        fresh = [row[:] for row in out]
        for q in range(1, n // s + 1):
            coefficient = comb(count + q - 1, q)
            for weight in range(n - q * s + 1):
                for b in range(weight + 1):
                    if out[weight][b]:
                        fresh[weight + q * s][b + q] += coefficient * out[weight][b]
        out = fresh
    return out


def check_root_tails(n=40, qmax=6):
    """Check the exact explicit nonnegative remainder, not just its valuation."""
    integer_range("root-tail N", n, 8, 64)
    integer_range("root-tail q_max", qmax, 0, (n - 8) // 4)
    series = universal_series(n)
    rooted = rooted_counts(n + 3)
    forest = root_forest_cycle(rooted, n)
    marked = marked_euler_product([0] + rooted[4:n + 4], n)
    require([sum(row) for row in marked] == series['J3'], "marked J3 specialization failed")
    require([sum(b * value for b, value in enumerate(row)) for row in marked] == series['J3v'],
            "marked J3 derivative specialization failed")
    results = []
    for q in range(qmax + 1):
        tail = [0] + [sum(forest[m][q:]) for m in range(n)]
        approx = add(shift(series['a'], q + 1), scale(shift(series['c'], 2 * q + 2), -1),
                     shift(add(scale(series['L'], q), series['Q']), 3 * q + 4))
        difference = add(tail, scale(approx, -1))
        explicit = [0] * (n + 1)
        # z^(3q+1) sum_(ell,t>=1) z^(2ell+t)(1+...+z^(ell-1))
        # sum_(b>=q+ell+t+2) (b-q-ell-t-1) [v^b] J3(z,v).
        for ell in range(1, n + 1):
            for t in range(1, n + 1):
                base = 3 * q + 1 + 2 * ell + t
                minimum_b = q + ell + t + 2
                if base + minimum_b > n:
                    break
                for weight in range(minimum_b, n - base + 1):
                    value = sum((b - q - ell - t - 1) * marked[weight][b]
                                for b in range(minimum_b, weight + 1))
                    if value:
                        for j in range(min(ell, n - base - weight + 1)):
                            explicit[base + weight + j] += value
        require(difference == explicit, f"explicit root-tail remainder mismatch at q={q}")
        require(all(x >= 0 for x in explicit), f"negative root-tail remainder at q={q}")
        first = next(((i, x) for i, x in enumerate(explicit) if x), None)
        require(first == (4 * q + 8, comb(q + 7, 3)), f"root-tail leading term mismatch at q={q}")
        results.append({'q': q, 'checked_through': n, 'first_remainder_degree': first[0],
                        'first_remainder_coefficient': first[1], 'remainder_coefficients': explicit})
    return {'status': 'pass', 'N': n, 'q_max': qmax, 'coefficient_checks': (qmax + 1) * (n + 1),
            'checks': results}


def check_literal_trees(n=12):
    """Enumerate actual canonical child-ID tuples, independently of generating series."""
    integer_range("literal tree cutoff", n, 1, MAX_LITERAL_N)
    tree_types, sizes, maxima, by_size = [], [], [], {}
    for size in range(1, n + 1):
        forests = []
        def visit(remaining, first, children):
            if remaining == 0:
                forests.append(tuple(children))
                return
            for index in range(first, len(tree_types)):
                if sizes[index] > remaining:
                    break
                visit(remaining - sizes[index], index, children + [index])
        visit(size - 1, 0, [])
        require(len(forests) == len(set(forests)), f"duplicate canonical tree at size {size}")
        counts = {}
        for children in forests:
            maximum = max([len(children)] + [maxima[index] for index in children])
            counts[maximum] = counts.get(maximum, 0) + 1
            tree_types.append(children)
            sizes.append(size)
            maxima.append(maximum)
        by_size[size] = counts
    checks = 0
    for cap in range(n):
        bounded = bounded_counts(n, cap)
        for size in range(1, n + 1):
            expected = sum(count for degree, count in by_size[size].items() if degree <= cap)
            require(bounded[size] == expected, f"literal-tree mismatch at size={size}, cap={cap}")
            checks += 1
    ordinary = rooted_counts(n)
    counts_by_size = {size: sum(counts.values()) for size, counts in by_size.items()}
    require(list(counts_by_size.values()) == ordinary[1:], "literal/unrestricted tree count mismatch")
    return {'status': 'pass', 'N': n, 'literal_tree_types': len(tree_types),
            'bounded_cycle_checks': checks, 'counts_by_size': counts_by_size,
            'maximum_degree_counts_by_size': by_size}
