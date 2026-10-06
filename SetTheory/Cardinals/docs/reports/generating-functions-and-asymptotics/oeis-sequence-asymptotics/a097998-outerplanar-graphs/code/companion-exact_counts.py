"""Exact, independent block recurrences; labeled counts; finite marker identities."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, factorial
from common import ROOT, require


def mul(a, b, n):
    return [sum((a[j] * b[k-j] for j in range(max(0, k-len(b)+1), min(k, len(a)-1)+1)), F(0)) for k in range(n+1)]


def exp0(a, n):
    require(a[0] == 0, 'Exponential series constant must vanish')
    out = [F(1)]
    for k in range(1, n+1):
        out.append(sum((j*a[j]*out[k-j] for j in range(1, min(k, len(a)-1)+1)), F(0))/k)
    return out


def radical_blocks(n):
    # r(u)^2=1-6u+u^2, r(0)=1. No Schroeder inputs.
    r = [F(1)]
    for k in range(1, n):
        target = -6 if k == 1 else 1 if k == 2 else 0
        r.append((target-sum((r[j]*r[k-j] for j in range(1, k)), F(0)))/2)
    beta = [0]
    for k in range(1, n):
        value = ((5 if k == 1 else 0)-r[k])*factorial(k)/8
        require(value.denominator == 1, 'Nonintegral radical block count')
        beta.append(value.numerator)
    return beta


def schroeder_blocks(n):
    # S=1+u S+u S^2 has coefficients 1,2,6,22,... (large Schroeder).
    # For k>=2, [u^k]b = S_{k-1}/4; equivalently half little-Schroeder.
    s = [1]
    for k in range(1, n-1):
        s.append(s[k-1]+sum(s[j]*s[k-1-j] for j in range(k)))
    beta = [0, 1][:n]
    for k in range(2, n):
        value = factorial(k)*s[k-1]
        require(value % 4 == 0, 'Nonintegral Schroeder block count')
        beta.append(value//4)
    return beta


def connected_bell(beta, n):
    # Integer exponential Bell recurrence followed by Lagrange inversion.
    c = [0]
    for m in range(1, n+1):
        e = [1]
        for k in range(1, m):
            e.append(m*sum(comb(k-1, j-1)*beta[j]*e[k-j] for j in range(1, k+1)))
        require(e[-1] % m == 0, 'Connected Lagrange divisibility failed')
        c.append(e[-1]//m)
    return c


def connected_ordinary(beta, n):
    # Separately coded ordinary rational exponential recurrence.
    b = [F(beta[j], factorial(j)) for j in range(len(beta))]
    c = [0]
    for m in range(1, n+1):
        h = [F(1)]
        for k in range(1, m):
            h.append(sum(F(m*j, k)*b[j]*h[k-j] for j in range(1, k+1)))
        value = F(factorial(m), m*m)*h[-1]
        require(value.denominator == 1, 'Nonintegral ordinary Lagrange count')
        c.append(value.numerator)
    return c


def all_counts(c):
    g = [1]
    for n in range(1, len(c)):
        g.append(sum(comb(n-1, k-1)*c[k]*g[n-k] for k in range(1, n+1)))
    return g


def fixture_rows(name):
    rows = {}
    for line in (ROOT / 'fixtures' / name).read_text().splitlines():
        if line and not line.startswith('#'):
            n, value = map(int, line.split())
            require(n not in rows, 'Duplicate OEIS index')
            rows[n] = value
    require(sorted(rows) == list(range(201)), 'Expected OEIS fixture indices 0..200')
    require(rows[0] == 1, 'Unexpected OEIS zero convention')
    return rows


def literal_counts(c, g):
    output = {}
    for n in range(1, 6):
        edges = list(combinations(range(n), 2))
        orders = [(0,)+p for p in permutations(range(1, n)) if n < 3 or p[0] < p[-1]]
        total = connected = 0
        for mask in range(1 << len(edges)):
            selected = [edge for j, edge in enumerate(edges) if mask >> j & 1]
            admitted = False
            for order in orders:
                position = {v: j for j, v in enumerate(order)}
                intervals = [tuple(sorted((position[a], position[b]))) for a, b in selected]
                if not any(a < c1 < b < d or c1 < a < d < b for (a, b), (c1, d) in combinations(intervals, 2)):
                    admitted = True
                    break
            if admitted:
                total += 1
                reached = {0}
                for _ in range(n):
                    for a, b in selected:
                        if a in reached:
                            reached.add(b)
                        if b in reached:
                            reached.add(a)
                connected += len(reached) == n
        require((connected, total) == (c[n], g[n]), 'Literal graph count mismatch')
        output[str(n)] = {'connected': connected, 'all': total, 'edge_sets_examined': 1 << len(edges)}
    return output


def marked_checks(c, g, beta):
    # SET convolution gives every coefficient of f_n(v) exactly through n=8.
    m = 8
    powers = [[1]+[0]*m]
    for k in range(1, m+1):
        old = powers[-1]
        powers.append([sum(comb(n, j)*old[n-j]*c[j] for j in range(1, n+1)) for n in range(m+1)])
    polynomials = {}
    b = [F(beta[j], factorial(j)) for j in range(m)]
    psi = [F(0)]+[F(1)]+[-F(k-1, k)*b[k-1] for k in range(2, m+1)]
    derivative = [k*psi[k] for k in range(1, m+1)]
    for n in range(1, m+1):
        coefficients = []
        for k in range(n+1):
            require(powers[k][n] % factorial(k) == 0, 'SET division failed')
            coefficients.append(powers[k][n]//factorial(k))
        require(coefficients[1] == c[n] and sum(coefficients) == g[n], 'Marker endpoints failed')
        # Degree <= n: n+1 distinct evaluations establish the polynomial identities.
        for v in range(n+1):
            exponent = [n*b[j]+v*psi[j] for j in range(m)]
            e = exp0(exponent, n-1)
            direct = F(factorial(n)*v, n)*mul(e, derivative, n-1)[n-1]
            h = [F(1)]+[v*k*psi[k] for k in range(1, m)]
            corrected = F(factorial(n)*v, n*n)*mul(e, h, n-1)[n-1]
            expected = sum(value*v**k for k, value in enumerate(coefficients))
            require(direct == corrected == expected, 'Exact marked Lagrange/IBP identity failed')
        polynomials[str(n)] = coefficients
    return {'identity_degree_bound': 'at most n, verified at v=0,...,n', 'component_polynomials_ascending_v': polynomials}


def run(n=200):
    require(8 <= n <= 240, 'Term bound must be 8..240')
    beta_r = radical_blocks(n)
    beta_s = schroeder_blocks(n)
    require(beta_r == beta_s, 'Independent block recurrences disagree')
    c = connected_bell(beta_r, n)
    c_other = connected_ordinary(beta_s, n)
    require(c == c_other, 'Independent connected count recurrences disagree')
    g = all_counts(c)
    checks = {}
    for seq, values in [('097998', c), ('098000', g)]:
        rows = fixture_rows('b'+seq+'.txt')
        for k in range(1, min(n, 200)+1):
            require(rows[k] == values[k], 'OEIS A'+seq+' mismatch at n='+str(k))
        checks['A'+seq] = {'positive_terms_matched': min(n, 200), 'fixture_zero': rows[0], 'egf_zero': values[0]}
    beginning = [str(F(beta_r[j], factorial(j))) for j in range(1, 6)]
    require(beginning == ['1', '1/2', '3/2', '11/2', '45/2'], 'Incorrect b-series beginning')
    return {'terms': n, 'b_series_u1_through_u5': beginning, 'oeis': checks,
            'literal_graphs': literal_counts(c, g), 'marked_identities': marked_checks(c, g, beta_r),
            'connected': [str(x) for x in c], 'all': [str(x) for x in g]}
