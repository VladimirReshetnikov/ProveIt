#!/usr/bin/env python3
"""Independent exact-integer algebra checks; Python standard library only.

No imports from the candidate or its dependencies, no program interpreter,
physical simulator, proof assistant, floating point, or network access.
Interpolants are reconstructed by division of the node product and scaled
Lagrange summation; the candidate's difference/Newton checker is not used.
"""
import argparse
import hashlib
import json
from math import comb, factorial
from pathlib import Path


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def root_product(nodes):
    p = [1]
    for node in nodes:
        q = [0] * (len(p) + 1)
        for j, coefficient in enumerate(p):
            q[j] -= node * coefficient
            q[j + 1] += coefficient
        p = q
    return p


def divide_linear(p, node):
    q = [0] * (len(p) - 1)
    q[-1] = p[-1]
    for j in range(len(q) - 2, -1, -1):
        q[j] = p[j + 1] + node * q[j + 1]
    require(p[0] + node * q[0] == 0, 'exact linear division')
    return q


def evaluate(p, node):
    result = 0
    for coefficient in reversed(p):
        result = result * node + coefficient
    return result


def affine_reflection(p, center_sum):
    # Horner composition p(center_sum - x), using exact integer coefficients.
    result = [0]
    for coefficient in reversed(p):
        new = [0] * (len(result) + 1)
        for j, value in enumerate(result):
            new[j] += center_sum * value
            new[j + 1] -= value
        new[0] += coefficient
        result = trim(new)
    return result


def interpolate(K):
    N = K * K
    R = root_product(range(1, N + 1))
    U, V = [0] * N, [0] * N
    for i in range(1, N + 1):
        weight = (-1) ** (N - i) * comb(N - 1, i - 1)
        basis = divide_linear(R, i)
        u, v = (i - 1) // K + 1, (i - 1) % K + 1
        for j, coefficient in enumerate(basis):
            U[j] += u * weight * coefficient
            V[j] += v * weight * coefficient
    return trim(U), trim(V), R


def add(*polynomials):
    result = {}
    for p in polynomials:
        for monomial, value in p.items():
            result[monomial] = result.get(monomial, 0) + value
    return {m: v for m, v in result.items() if v}


def scale(p, value):
    return {m: v * value for m, v in p.items() if v * value}


def multiply(p, q):
    result = {}
    for m, a in p.items():
        for n, b in q.items():
            exponent = tuple(x + y for x, y in zip(m, n))
            require(len(m) == len(n), 'consistent variable dimensions')
            result[exponent] = result.get(exponent, 0) + a * b
    return {m: v for m, v in result.items() if v}


def square(p):
    return multiply(p, p)


def constant(value, dimensions):
    return {(0,) * dimensions: value} if value else {}


def variable(index, dimensions):
    e = [0] * dimensions
    e[index] = 1
    return {tuple(e): 1}


def univariate(p, index, dimensions):
    result = {}
    for degree, coefficient in enumerate(p):
        if coefficient:
            exponent = [0] * dimensions
            exponent[index] = degree
            result[tuple(exponent)] = coefficient
    return result


def degree(p):
    return max((sum(m) for m in p), default=-1)


def top(p):
    d = degree(p)
    return {m: v for m, v in p.items() if sum(m) == d}


def hash_polynomial(p):
    canonical = json.dumps([[list(m), str(v)] for m, v in sorted(p.items())],
                           separators=(',', ':')).encode()
    return hashlib.sha256(canonical).hexdigest()


def expected_degree(K):
    return 0 if K == 1 else K * K - (1 if K % 2 == 0 else 2)


def boundary_lead(K):
    if K == 1:
        return 1
    N = K * K
    if K % 2 == 0:
        return -sum(comb(N - 2, h * K - 1) for h in range(1, K))
    return (N - 1) * sum((-1) ** (h + 1) * comb(N - 3, h * K - 1)
                         for h in range(1, K))


def top_two_from_lagrange(K):
    # A basis numerator has top coefficients 1 and i - sum(1..N).
    N = K * K
    total_nodes = N * (N + 1) // 2
    first_u = second_u = first_v = second_v = 0
    choose = 1
    for i in range(1, N + 1):
        weight = choose if (N - i) % 2 == 0 else -choose
        u, v = (i + K - 1) // K, i + K - K * ((i + K - 1) // K)
        first_u += weight * u
        first_v += weight * v
        second_u += weight * u * (i - total_nodes)
        second_v += weight * v * (i - total_nodes)
        if i < N:
            choose = choose * (N - i) // i
    return first_u, second_u, first_v, second_v


def check_large_range():
    rows = []
    for K in range(1, 102):
        upper_u, next_u, upper_v, next_v = top_two_from_lagrange(K)
        a = boundary_lead(K)
        if K == 1:
            require((upper_u, upper_v) == (1, 1), 'K=1 constants')
        elif K % 2 == 0:
            require(upper_u == a and upper_v == -K * a and a < 0,
                    'even Lagrange top coefficient')
        else:
            require(upper_u == upper_v == 0, 'odd leading cancellation')
            require(next_u == a and next_v == -K * a, 'odd second coefficient')
            require(a * (-1) ** ((K + 1) // 2) > 0, 'odd sign')
            # Exact reduction of x(1+x)^(K^2-3) modulo x^K+1.
            n, filtered_constant, choose = K * K - 3, 0, 1
            for j in range(n + 1):
                if (j + 1) % K == 0:
                    filtered_constant += (-1) ** ((j + 1) // K) * choose
                if j < n:
                    choose = choose * (n - j) // (j + 1)
            require(-(K * K - 1) * filtered_constant == a, 'algebraic root filter')
        require(a != 0, 'nonzero integer leading coefficient')
        rows.append({'K': K, 'degree': expected_degree(K),
                     'leading_coefficient': str(a), 'coefficient_bits': abs(a).bit_length()})
    return rows


def allowed_support(m, d):
    A, B, j, r, s = m
    if A == B == r == s == 0:
        return j <= 4 * d
    if (A, B, r, s) in [(2, 0, 0, 0), (0, 2, 0, 0)]:
        return j <= 2 * d
    if (A, B, r, s) in [(1, 0, 0, 0), (0, 1, 0, 0)]:
        return j <= 3 * d
    if (A, B, r, s) in [(0, 0, 1, 0), (0, 0, 0, 1)]:
        return j <= d
    return j == 0 and (A, B, r, s) in [
        (0, 0, 2, 0), (0, 0, 0, 2), (1, 0, 1, 0), (0, 1, 0, 1)]


def subsets(K):
    N = K * K
    if K <= 3:
        return [tuple(i + 1 for i in range(N) if mask >> i & 1)
                for mask in range(1 << N)]
    return sorted(set([(), tuple(range(1, N + 1)), (1,), (N,),
                       tuple(range(1, N + 1, 2)), tuple(range(K, N + 1, K)),
                       tuple(range(1, K + 1))]))


def check_full_polynomials():
    interpolation_rows, sos_rows = [], []
    node_count = 0
    for K in range(1, 11):
        N, c, d = K * K, factorial(K * K - 1), expected_degree(K)
        U, V, R = interpolate(K)
        require(len(U) - 1 == len(V) - 1 == d, 'full interpolant degree')
        require(U[-1] == boundary_lead(K), 'full leading coefficient')
        for i in range(1, N + 1):
            require(evaluate(U, i) == c * ((i + K - 1) // K), 'U node')
            require(evaluate(V, i) == c * ((i - 1) % K + 1), 'V node')
            node_count += 1
        reflected = affine_reflection(U, N + 1)
        reflection_target = [-x for x in U]
        reflection_target[0] += c * (K + 1)
        require(reflected == trim(reflection_target), 'full reflection identity')
        if K >= 2:
            target = [-K * coefficient for coefficient in U]
            target[0] += c * K
            target[1] += c
            require(V == trim(target), 'full V=c(z+K)-KU identity')
        interpolation_rows.append({'K': K, 'degree': d, 'nodes_checked': N,
                                   'U0': [str(v) for v in U], 'V0': [str(v) for v in V]})
        if K > 8:
            continue
        A, B, j, r, s = [variable(i, 5) for i in range(5)]
        one = constant(1, 5)
        u, v, range_poly = [univariate(p, 2, 5) for p in (U, V, R)]
        residuals = [range_poly,
            multiply(add(scale(A, c), scale(u, -1)), add(u, constant(-c*K, 5))),
            add(scale(A, c), scale(u, -1), scale(r, -c), scale(one, c)),
            multiply(add(scale(B, c), scale(v, -1)), add(v, constant(-c*K, 5))),
            add(scale(B, c), scale(v, -1), scale(s, -c), scale(one, c))]
        base = add(*(square(p) for p in residuals))
        for accepted in subsets(K):
            h = univariate(root_product(accepted), 2, 5)
            P = add(base, square(h))
            if K == 1:
                require(degree(P) == 2 and len(P) == 9, 'K=1 SOS')
            else:
                a = U[-1]
                require(degree(P) == 4 * d, 'exact SOS degree')
                require(top(P) == {(0, 0, 4*d, 0, 0): (1 + K**4) * a**4},
                        'entire SOS top homogeneous part')
                require(len(P) <= 16 * d + 11, 'sharpened support count')
                require(all(allowed_support(m, d) for m in P), 'disjoint support types')
            sos_rows.append({'K': K, 'accepted_nodes': list(accepted),
                             'degree': degree(P), 'support': len(P),
                             'expanded_polynomial_sha256': hash_polynomial(P)})
    return interpolation_rows, sos_rows, node_count


def check_power_degrees():
    names = ['o', 'w', 'M', 'g', 'x', 'y', 'u', 'v', 's', 't', 'qb', 'qv', 'J',
             'alpha_plus', 'beta_plus', 'dwb_plus', 'dwk_plus', 'dyk_plus',
             'a1_plus', 'a2_plus', 's1_plus', 's2_plus', 't1_plus', 't2_plus',
             'r1_plus', 'r2_plus', 'C']
    D = len(names)
    p = {name: variable(i, D) for i, name in enumerate(names)}
    one = constant(1, D)
    alpha, beta = add(p['alpha_plus'], one), add(p['beta_plus'], one)
    aliases = {name: add(p[name + '_plus'], scale(one, -1))
               for name in ['dwb', 'dwk', 'dyk', 'a1', 'a2', 's1', 's2', 't1', 't2', 'r1', 'r2']}
    def pell(x, y, a):
        return add(square(x), scale(one, -1), scale(multiply(add(square(a), scale(one, -1)), square(y)), -1))
    E = [pell(p['x'], p['y'], alpha), pell(p['u'], p['v'], alpha), pell(p['s'], p['t'], beta),
         add(beta, scale(one, -1), scale(multiply(p['y'], p['qb']), -4)),
         add(beta, multiply(p['u'], aliases['a1']), scale(alpha, -1), scale(multiply(p['u'], aliases['a2']), -1)),
         add(p['v'], scale(multiply(square(p['y']), p['qv']), -1)),
         add(p['s'], multiply(p['u'], aliases['s1']), scale(p['x'], -1), scale(multiply(p['u'], aliases['s2']), -1)),
         add(p['t'], scale(multiply(p['y'], aliases['t1']), 4), scale(p['C'], -1), scale(multiply(p['y'], aliases['t2']), -4)),
         add(p['y'], scale(p['C'], -1), scale(aliases['dyk'], -1)),
         add(p['w'], scale(one, -2), scale(aliases['dwb'], -1)),
         add(p['w'], scale(p['C'], -1), scale(aliases['dwk'], -1)),
         add(p['M'], scale(p['o'], -2), scale(p['J'], -1)),
         add(square(alpha), scale(one, -1), scale(multiply(add(square(add(p['w'], one)), scale(one, -1)), square(multiply(p['w'], p['g']))), -1)),
         add(scale(alpha, 4), scale(p['M'], -1), scale(one, -5)),
         add(p['x'], multiply(p['M'], aliases['r1']), scale(multiply(p['y'], add(alpha, scale(one, -2))), -1), scale(p['o'], -2), scale(multiply(p['M'], aliases['r2']), -1))]
    actual = [degree(e) for e in E]
    require(actual == [4, 4, 4, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 2], 'all POWER degrees')
    top_E13 = scale(multiply(square(square(p['w'])), square(p['g'])), -1)
    require(top(E[12]) == top_E13, 'E13 entire degree-six part')
    base = add(*(square(e) for e in E))
    require(top(base) == square(top_E13), 'POWER entire degree-twelve part')
    return {'residual_degrees': actual, 'module_sum_degree': degree(base),
            'top_coefficient': 1, 'top_w_exponent': 8, 'top_g_exponent': 4,
            'module_sum_sha256': hash_polynomial(base)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='independent_results.json')
    args = parser.parse_args()
    top_rows = check_large_range()
    interpolants, sos, node_count = check_full_polynomials()
    power = check_power_degrees()
    result = {'status': 'PASS', 'arithmetic': 'exact Python integers; no floating point',
              'large_range': [1, 101], 'full_interpolation_range': [1, 10],
              'complete_SOS_range': [1, 8], 'exhaustive_acceptance_K': [1, 2, 3],
              'K_values_checked': len(top_rows), 'interpolation_nodes_checked': node_count,
              'SOS_expansions_checked': len(sos), 'top_coefficient_checks': top_rows,
              'full_interpolants': interpolants, 'SOS_checks': sos, 'POWER_degree_checks': power,
              'scope': 'Finite exact checks support, and do not replace, the all-K proof audit.'}
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'K_values_checked',
                     'interpolation_nodes_checked', 'SOS_expansions_checked']}, sort_keys=True))


if __name__ == '__main__':
    main()
