#!/usr/bin/env python3
"""Exact finite implementations illustrating the proved operator/logic rules.

These are implementation checks, not a proof checker for iPRA or a substitute
for the universal arguments in the report. Python standard library only.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def dot(a, b):
    assert len(a) == len(b)
    return sum((x * y for x, y in zip(a, b)), F(0))


def matvec(a, x):
    return [dot(row, x) for row in a]


def multiply(a, b):
    assert a and b and len(a[0]) == len(b)
    return [[sum((a[i][j] * b[j][k] for j in range(len(b))), F(0))
             for k in range(len(b[0]))] for i in range(len(a))]


def push(mu, p):
    return [sum((mu[i] * p[i][j] for i in range(len(mu))), F(0))
            for j in range(len(p[0]))]


def l1(w, x):
    return dot(w, [abs(t) for t in x])


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def clip(k, x):
    return max(-k, min(k, x))


def tail(w, x, k):
    return dot(w, [max(abs(t) - k, F(0)) for t in x])


def valid_kernel(mu, p, nu):
    return (sum(mu) == 1 and sum(nu) == 1 and len(mu) == len(p)
            and all(x >= 0 for x in mu + nu)
            and all(len(row) == len(nu) and sum(row) == 1
                    and all(x >= 0 for x in row) for row in p)
            and push(mu, p) == nu)


def tensor(a, b):
    return [[a[i][j] * b[k][ell]
             for j in range(len(a[0])) for ell in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def posterior(a):
    mass = sum(a)
    assert mass > 0
    return [x / mass for x in a]


def backwards_influence(rows, output):
    """Rows store nonnegative coefficients of strictly earlier vertices."""
    influence = [F(0) for _ in rows]
    influence[output] = F(1)
    for v in range(len(rows) - 1, -1, -1):
        for u, weight in rows[v].items():
            assert 0 <= u < v and weight >= 0
            influence[u] += influence[v] * weight
    return influence


def forward_budget(rows, local):
    result = []
    for v, row in enumerate(rows):
        result.append(local[v] + sum((a * result[u] for u, a in row.items()), F(0)))
    return result


def evaluate(formula, env, points, weights):
    """Small explicit binder-preserving AST; names are local variable slots."""
    tag, *args = formula
    if tag == 'absdiff':
        return abs(env[args[0]] - env[args[1]])
    if tag == 'constant':
        return F(args[0])
    if tag in ('mean', 'sup', 'inf'):
        variable, child = args
        values = [evaluate(child, dict(env, **{variable: x}), points, weights)
                  for x in points]
        if tag == 'mean':
            return dot(weights, values)
        return max(values) if tag == 'sup' else min(values)
    raise ValueError(tag)


def main():
    checks = 0
    mu = [F(1, 3), F(2, 3)]
    p = [[F(1, 2), F(1, 3), F(1, 6)], [F(1, 4), F(1, 4), F(1, 2)]]
    nu = push(mu, p)
    q = [[F(1, 3), F(2, 3)], [F(3, 4), F(1, 4)], [F(1, 5), F(4, 5)]]
    xi = push(nu, q)
    assert valid_kernel(mu, p, nu) and valid_kernel(nu, q, xi)
    pq = multiply(p, q)
    assert valid_kernel(mu, pq, xi)
    checks += 3
    for a in range(-4, 5):
        for b in range(-4, 5):
            f = [F(a), F(b)]
            assert matvec(pq, f) == matvec(p, matvec(q, f))
            assert l1(mu, matvec(pq, f)) <= l1(xi, f)
            assert dot(mu, matvec(pq, f)) == dot(xi, f)
            checks += 3
    product_mu = [a * b for a in mu for b in nu]
    product_nu = [a * b for a in nu for b in xi]
    assert valid_kernel(product_mu, tensor(p, q), product_nu)
    checks += 1

    # Same-marginal kernels: identity versus independent resampling.
    w = [F(1, 2), F(1, 4), F(1, 4)]
    ident = [[F(int(i == j)) for j in range(3)] for i in range(3)]
    redraw = [w[:] for _ in range(3)]
    delta = sum(w[i] * sum(abs(ident[i][j] - redraw[i][j]) for j in range(3))
                for i in range(3))
    kernel_cases = []
    for f in ([F(0), F(4), F(16)], [F(-20), F(0), F(7)], [F(1)] * 3):
        actual = l1(w, sub(matvec(ident, f), matvec(redraw, f)))
        for k in (F(1), F(4), F(8), F(32)):
            bound = 2 * tail(w, f, k) + k * delta
            assert actual <= bound
            kernel_cases.append({'values': f, 'cutoff': k, 'error': actual, 'bound': bound})
            checks += 1

    for a, b in (([F(3, 10), F(7, 10)], [F(2, 5), F(3, 5)]),
                 ([F(1, 1024), F(0)], [F(0), F(1, 1024)])):
        tau = min(sum(a), sum(b))
        delta_row = sum(abs(x - y) for x, y in zip(a, b))
        post_error = sum(abs(x - y) for x, y in zip(posterior(a), posterior(b)))
        assert post_error <= 2 * delta_row / tau
        checks += 1
    rare_conditioning = {'input_distance': F(1, 512), 'posterior_distance': F(2)}

    # Each conditional projection misses a normalized finer Haar function.
    for level in range(8):
        haar = [F(1) if i % 2 == 0 else F(-1) for i in range(2 ** (level + 1))]
        average = [(haar[2 * i] + haar[2 * i + 1]) / 2 for i in range(2 ** level)]
        assert all(x == 0 for x in average)
        assert sum(abs(x) for x in haar) / len(haar) == 1
        checks += 2

    # Influence accounts for a shared subexpression used on two paths.
    rows = [{}, {}, {0: F(99, 100), 1: F(1, 100)}, {0: F(1), 2: F(1)}]
    local = [F(1, 1024), F(1, 16), F(1, 4096), F(0)]
    lam = backwards_influence(rows, 3)
    forward = forward_budget(rows, local)
    assert forward[3] == dot(lam, local)
    assert lam == [F(199, 100), F(1, 100), F(1), F(1)]
    checks += 2

    formulas = {
        'sup_mean': ('sup', 'y', ('mean', 'x', ('absdiff', 'x', 'y'))),
        'mean_sup': ('mean', 'x', ('sup', 'y', ('absdiff', 'x', 'y'))),
        'mean_mean': ('mean', 'x', ('mean', 'y', ('absdiff', 'x', 'y'))),
        'mean_mean_swapped': ('mean', 'y', ('mean', 'x', ('absdiff', 'x', 'y'))),
    }
    formula_rows = []
    for m in (2, 4, 8, 16, 32, 64):
        points = [F(2 * i + 1, 2 * m) for i in range(m)]
        weights = [F(1, m)] * m
        values = {key: evaluate(ast, {}, points, weights) for key, ast in formulas.items()}
        assert values['sup_mean'] == F(1, 2) - F(1, 2 * m)
        assert values['mean_sup'] == F(3, 4) - F(1, 2 * m)
        assert values['mean_mean'] == F(1, 3) - F(1, 3 * m * m)
        assert values['mean_mean'] == values['mean_mean_swapped']
        assert values['mean_sup'] - values['sup_mean'] == F(1, 4)
        formula_rows.append({'nodes': m, **values})
        checks += 5

    # Normalization with inaccurate masses; proof's 2*L1 input error bound.
    true_masses = [F(1, 4), F(1, 2), F(1, 4)]
    for perturb in ([F(1, 100), F(-1, 100), F(1, 100)],
                    [F(-1, 8), F(-1, 8), F(-1, 8)],
                    [F(0)] * 3):
        raw = [max(F(0), a + d) for a, d in zip(true_masses, perturb)]
        norm = posterior(raw)
        initial_error = sum(abs(a - b) for a, b in zip(raw, true_masses))
        final_error = sum(abs(a - b) for a, b in zip(norm, true_masses))
        assert final_error <= 2 * initial_error
        checks += 1

    result = {'status': 'passed', 'exact_assertions': checks,
              'scope': 'Finite rational implementation examples; not universal or object-iPRA proofs.',
              'marginals': {'mu': mu, 'nu': nu, 'xi': xi},
              'kernel_tail_examples': kernel_cases,
              'rare_conditioning': rare_conditioning,
              'dag': {'influence': lam, 'local_errors': local, 'root_error': forward[3]},
              'formula_values': formula_rows}
    out = Path(__file__).resolve().parents[1] / 'validation' / 'operator_logic_examples.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, default=str, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'exact_assertions': checks, 'output': str(out)}))


if __name__ == '__main__':
    main()
