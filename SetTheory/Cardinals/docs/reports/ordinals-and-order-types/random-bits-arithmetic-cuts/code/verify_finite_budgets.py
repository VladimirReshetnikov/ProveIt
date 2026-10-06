"""Exact finite checks and publication figures for candidate-budget theorems.

Run: python verify_finite_budgets.py

Outputs are written alongside this script.  Exhaustive checks use exact
rational arithmetic; plots use the exact Hamming-layer formula evaluated
with SciPy binomial probabilities.  Nothing in this program simulates a
nonstandard model or verifies an infinite-model assertion.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
from math import comb, exp, factorial, log, sqrt
import csv
import json
import platform

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
import scipy
from scipy.stats import binom, norm

ROOT = Path(__file__).resolve().parent
FIGS = ROOT / 'figures'
DATA = ROOT / 'data'
FIGS.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)


def exact_prefix_masses(biases):
    atoms = []
    for word in product((0, 1), repeat=len(biases)):
        mass = Fraction(1)
        for x, p in zip(word, biases):
            mass *= p if x else 1-p
        atoms.append(mass)
    atoms.sort(reverse=True)
    prefix = [Fraction(0)]
    for atom in atoms:
        prefix.append(prefix[-1] + atom)
    assert prefix[-1] == 1
    return prefix


def layer_exact(n, k, p):
    result = Fraction(0)
    remaining = k
    for r in range(n + 1):
        count = min(remaining, comb(n, r))
        result += count * p**r * (1-p)**(n-r)
        remaining -= count
        if not remaining:
            return result
    return result


def layer_float(n, k, p):
    """Exact optimal-list formula, with floating probability evaluation."""
    if k >= 2**n:
        return 1.0
    before = 0
    for r in range(n + 1):
        layer = comb(n, r)
        if k <= before + layer:
            theta = (k-before)/layer
            return float(binom.cdf(r-1, n, p) + theta*binom.pmf(r, n, p))
        before += layer
    raise AssertionError('Unreachable')


def check_pairwise_extremizers():
    """Exact primal witnesses and dual certificates, for both parities."""
    distributions = 0
    marginal_equalities = 0
    joint_equalities = 0
    dual_point_inequalities = 0
    for n in range(1, 11):
        if n % 2:
            a = (n+1)//2
            q = Fraction(1, n+1)
            weight_masses = {0: q, a: 1-q}
            dual = lambda w: Fraction((w-a)**2, a*a)
        else:
            a = n//2
            q = Fraction(1, n+2)
            weight_masses = {0: q, a: Fraction(1, 2),
                             a+1: Fraction(n, 2*(n+2))}
            dual = lambda w: Fraction((w-a)*(w-a-1), a*(a+1))

        word_masses = []
        for word in product((0, 1), repeat=n):
            weight = sum(word)
            mass = weight_masses.get(weight, Fraction(0))/comb(n, weight)
            word_masses.append((word, mass))
        assert sum((mass for _, mass in word_masses), Fraction(0)) == 1
        assert max(mass for _, mass in word_masses) == q
        assert word_masses[0][1] == q
        distributions += 1
        for i in range(n):
            assert sum((mass for word, mass in word_masses if word[i]),
                       Fraction(0)) == Fraction(1, 2)
            marginal_equalities += 1
            for j in range(i+1, n):
                for u, v in product((0, 1), repeat=2):
                    assert sum((mass for word, mass in word_masses
                                if word[i] == u and word[j] == v),
                               Fraction(0)) == Fraction(1, 4)
                    joint_equalities += 1
        for w in range(n+1):
            assert dual(w) >= (1 if w == 0 else 0)
            dual_point_inequalities += 1
        # Pairwise independence fixes every quadratic moment, so this is
        # the expected dual polynomial under any admissible distribution.
        expected_dual = sum((Fraction(comb(n, w), 2**n)*dual(w)
                             for w in range(n+1)), Fraction(0))
        assert expected_dual == q
    return {'extremizing_distributions': distributions,
            'fair_marginal_equalities': marginal_equalities,
            'pair_joint_probability_equalities': joint_equalities,
            'dual_pointwise_majorant_inequalities': dual_point_inequalities,
            'exact_dual_expectation_equalities': distributions}


def check_all():
    iid_cases = 0
    for n in range(1, 11):
        for p in (Fraction(1, 10), Fraction(1, 3), Fraction(1, 2)):
            exact = exact_prefix_masses([p]*n)
            for k in range(1, 2**n + 1):
                assert exact[k] == layer_exact(n, k, p), (n, k, p)
                iid_cases += 1

    # Independently enumerate nonidentical product atoms.  Check all budget
    # values on all finite pairs of lengths, against both sides of the
    # projection/modal-extension inequality used in the infinite bridge.
    biases = [Fraction(1, i+3) for i in range(8)]
    concentration = {n: exact_prefix_masses(biases[:n]) for n in range(1, 9)}
    product_cases = 0
    for lower in range(1, 8):
        for upper in range(lower+1, 9):
            modal_tail = Fraction(1)
            tail_sum = sum(biases[lower:upper], Fraction(0))
            for p in biases[lower:upper]:
                modal_tail *= 1-p
            for k in range(1, 2**lower+1):
                ql, qu = concentration[lower][k], concentration[upper][k]
                assert modal_tail*ql <= qu <= ql
                assert 0 <= ql-qu <= tail_sum
                product_cases += 1

    float_cases = 0
    max_float_error = 0.0
    for n in range(1, 11):
        for p in (Fraction(1, 10), Fraction(1, 3), Fraction(1, 2)):
            for k in sorted({1, 2**(n-1), 2**n-1, 2**n}):
                actual = layer_float(n, k, float(p))
                expected = float(layer_exact(n, k, p))
                max_float_error = max(max_float_error, abs(actual-expected))
                assert abs(actual-expected) < 2e-14
                float_cases += 1
    return {
        'exact_iid_budget_cases': iid_cases,
        'exact_nonidentical_projection_extension_cases': product_cases,
        'floating_evaluator_spot_checks': float_cases,
        'largest_float_absolute_error': max_float_error,
        'pairwise_fair_atom_bound_checks': check_pairwise_extremizers(),
        'scope': ('Finite binary distributions only. These checks do not '
                  'simulate nonstandard arithmetic, verify infinite-model '
                  'theorems, or establish mathematical novelty.'),
        'versions': {'python': platform.python_version(),
                     'numpy': np.__version__,
                     'scipy': scipy.__version__,
                     'matplotlib': matplotlib.__version__}
    }


def write_csv(name, fields, rows):
    with (DATA/name).open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def style():
    plt.rcParams.update({
        'font.family': 'DejaVu Sans',
        'font.size': 10,
        'axes.titlesize': 11,
        'axes.labelsize': 10,
        'legend.fontsize': 8,
        'axes.spines.top': False,
        'axes.spines.right': False,
        'axes.linewidth': 0.7,
        'grid.alpha': 0.18,
        'pdf.fonttype': 42,
        'savefig.facecolor': 'white',
    })


def save(fig, stem):
    fig.savefig(FIGS/f'{stem}.pdf', bbox_inches='tight')
    fig.savefig(FIGS/f'{stem}.png', dpi=180, bbox_inches='tight')
    plt.close(fig)


def sparse_figures():
    colors = ['#5694A4', '#CF8542', '#3D4F86']
    fig, axes = plt.subplots(1, 2, figsize=(8.5, 3.25))
    rows = []
    beta_values = np.linspace(0, 4, 401)
    for n, color in zip((100, 1000, 10000), colors):
        ys = []
        for beta in beta_values:
            k = max(1, int(n**float(beta)))
            q = layer_float(n, k, 1/n)
            ys.append(q)
            rows.append({'N': n, 'lambda': 1, 'beta': f'{beta:.6f}',
                         'K': k, 'capture_probability': f'{q:.14g}'})
        axes[0].plot(beta_values, ys, color=color, lw=1.5, label=f'N = {n:,}')
    xs = np.arange(0, 5)
    limits = [exp(-1)*sum(1/factorial(j) for j in range(r+1)) for r in xs]
    axes[0].step(xs, limits, where='post', color='#20252D', lw=1.2,
                 ls='--', label='Poisson limit')
    axes[0].set(xlim=(0, 4), ylim=(0.32, 1.01),
                xlabel=r'Budget exponent $\beta=\log_N K$',
                ylabel='Optimal captured probability',
                title=r'(a) Sparse noise: $p=1/N$')
    axes[0].set_xticks(range(5))
    axes[0].grid(axis='y')
    axes[0].legend(loc='lower right', frameon=False)

    local_rows = []
    kappas = np.linspace(0.02, 1.5, 297)
    for r, color in ((1, colors[0]), (2, colors[2])):
        theory = [exp(-1)*(sum(1/factorial(j) for j in range(r))
                            + min(kap*factorial(r), 1)/factorial(r))
                  for kap in kappas]
        axes[1].plot(kappas, theory, color=color, lw=1.7,
                     label=fr'$r={r}$, limit')
        for n, ls in ((100, ':'), (10000, '--')):
            ys = []
            for kap in kappas:
                k = max(1, int(float(kap)*n**r))
                q = layer_float(n, k, 1/n)
                ys.append(q)
                local_rows.append({'N': n, 'lambda': 1, 'r': r,
                                   'kappa': f'{kap:.9g}', 'K': k,
                                   'capture_probability': f'{q:.14g}'})
            # N=100 curves show finite convergence visibly; N=10000
            # overlays the limiting lines and is saved in the data.
            if n == 100:
                axes[1].plot(kappas, ys, color=color, lw=1, ls=ls,
                             label=fr'$r={r}$, $N=100$')
    axes[1].set(xlim=(0, 1.5), ylim=(0.32, 1.01),
                xlabel=r'Critical multiplier $\kappa$ in $K\sim\kappa N^r$',
                title='(b) The resolved jump window')
    axes[1].grid(axis='y')
    axes[1].legend(loc='lower right', frameon=False)
    fig.tight_layout(w_pad=2.1)
    save(fig, 'sparse_budget_staircase')
    write_csv('sparse_exponent.csv', list(rows[0]), rows)
    write_csv('sparse_critical_window.csv', list(local_rows[0]), local_rows)

    # A short inspectable convergence table at representative layer budgets.
    table = []
    for r, kap in ((1, 0.25), (1, 1.0), (2, 0.25), (2, 0.5), (3, 1/6)):
        limit = exp(-1)*(sum(1/factorial(j) for j in range(r))
                          + min(kap*factorial(r), 1)/factorial(r))
        for n in (10, 100, 1000, 10000):
            k = max(1, int(kap*n**r))
            q = layer_float(n, k, 1/n)
            table.append({'lambda': 1, 'r': r, 'kappa': kap,
                          'N': n, 'K': k, 'capture_probability': q,
                          'Poisson_limit': limit, 'error': q-limit})
    write_csv('sparse_convergence_table.csv', list(table[0]), table)


def entropy_figure():
    p = 0.1
    h = -p*log(p)-(1-p)*log(1-p)
    v = p*(1-p)*log((1-p)/p)**2
    colors = ['#5694A4', '#CF8542', '#3D4F86']
    fig, ax = plt.subplots(figsize=(6.3, 3.55))
    rows = []
    svalues = np.linspace(-3.5, 3.5, 351)
    for n, color in zip((100, 400, 1600), colors):
        ys = []
        for s in svalues:
            log_budget = n*h + sqrt(n*v)*float(s) - 0.5*log(n)
            k = max(1, int(exp(log_budget)))
            q = layer_float(n, k, p)
            ys.append(q)
            rows.append({'N': n, 'p': p, 's': f'{s:.9g}',
                         'log_K': f'{log(k):.14g}',
                         'capture_probability': f'{q:.14g}',
                         'normal_CDF': f'{norm.cdf(s):.14g}'})
        ax.plot(svalues, ys, color=color, lw=1.6, label=f'N = {n:,}')
    ax.plot(svalues, norm.cdf(svalues), color='#20252D', lw=1.2,
            ls='--', label=r'$\Phi(s)$')
    ax.set(xlim=(-3.5, 3.5), ylim=(-0.01, 1.01),
           xlabel=r'$s=(\log K-Nh(p)+\frac{1}{2}\log N)/\sqrt{Nv(p)}$',
           ylabel='Optimal captured probability',
           title=r'Fixed bias $p=0.1$: the normal candidate-budget transition')
    ax.grid(axis='y')
    ax.legend(loc='lower right', frameon=False)
    fig.tight_layout()
    save(fig, 'fixed_bias_normal_transition')
    write_csv('fixed_bias_normal_transition.csv', list(rows[0]), rows)


if __name__ == '__main__':
    checks = check_all()
    style()
    sparse_figures()
    entropy_figure()
    (ROOT/'finite_budget_verification.json').write_text(json.dumps(checks, indent=2)+'\n')
    print(json.dumps(checks, indent=2))
    print('Figures and CSV tables written beside this script in figures/ and data/.')
