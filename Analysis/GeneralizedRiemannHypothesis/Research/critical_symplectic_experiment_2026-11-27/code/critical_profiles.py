#!/usr/bin/env python3
"""Evaluate the proved critical laws; no Monte Carlo is used in this file.

Requires mpmath and matplotlib. Run from anywhere. Outputs are relative to
the containing research package. All quantities are asymptotic in even n.
"""
from pathlib import Path
import csv
import json
import math
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


class CriticalLaw:
    def __init__(self, q, precision=90, product_terms=400):
        self.q = int(q)
        self.precision = precision
        self.terms = product_terms
        mp.mp.dps = precision
        self.g = [mp.mpf(1)]
        for j in range(1, product_terms + 1):
            self.g.append(self.g[-1] * (1 - mp.mpf(q) ** (-j)))
        self.ginf = self.g[-1]
        self.odd = mp.fprod(1 - mp.mpf(q) ** (-(2*j-1))
                           for j in range(1, product_terms + 1))
        self.c = self.odd / (1 - mp.mpf(1)/q)

    def pi(self, b, k):
        if k < max(0, -b):
            return mp.mpf(0)
        return self.ginf * mp.mpf(self.q) ** (-k*(k+b)) / (self.g[k]*self.g[k+b])

    def points(self, k):
        return (self.q**k - 1)//(self.q - 1)

    def binomial_cdf(self, count, r):
        if r < 0:
            return mp.mpf(0)
        if r >= count:
            return mp.mpf(1)
        p = self.odd
        term = (1-p)**count
        value = term
        for j in range(r):
            term *= (count-j)*p / ((j+1)*(1-p))
            value += term
        return value

    def tail_bound(self, b, cutoff):
        """Upper bound on sum_{k>=cutoff} pi_b(k), with product truncation ignored."""
        if cutoff < max(0, -b) or 2*cutoff+b+1 <= 0:
            raise ValueError("cutoff outside the decreasing tail")
        q = mp.mpf(self.q)
        return q**(-cutoff*(cutoff+b))/(self.ginf*(1-q**(-(2*cutoff+b+1))))

    def profile(self, a, cutoff=30):
        q = self.q
        mean = self.c*mp.mpf(q)**(-a)
        r = int(mp.ceil(mean))-1
        tv = recovery = unique = mass = first = second = third = mp.mpf(0)
        for k in range(max(0, 1-a), cutoff):
            p = self.pi(a-1, k)
            m = self.points(k)
            cdf = self.binomial_cdf(m, r)
            lower_mean = m*self.odd*self.binomial_cdf(m-1, r-1) if m else 0
            tv += p*(cdf-lower_mean/mean)
            recovery += p*(1-(1-self.odd)**m)/mean
            if k:
                unique += self.pi(a, k-1)*(1-self.odd)**(m-1)
            mass += p
            first += p*m*self.odd
            second += p*m*(m-1)*self.odd**2
            third += p*m*(m-1)*(m-2)*self.odd**3
        dim_tv = (mp.mpf(q)**(a-1)*self.ginf/self.g[1-a]
                  if a <= 0 else self.ginf/self.g[a-1])
        linear = self.ginf/self.g[a] if a >= 0 else mp.mpf(0)
        tol = mp.mpf('1e-65')
        assert abs(mass-1) < tol
        assert abs(first-mean) < tol
        assert abs(second-mean**2) < tol
        assert abs(third-(mean**3+(q-1)*self.odd*mean**2)) < tol
        assert tv > dim_tv
        assert recovery >= unique > linear
        if a >= 0:
            assert abs(recovery-(1-tv)/mean) < tol
        return dict(q=q, a=a, mean=mean, full_tv=tv, dimension_tv=dim_tv,
                    testing_success=(1+tv)/2, bayes_recovery=recovery,
                    unique_nondegenerate=unique, linear_recovery=linear,
                    nullity_tail_bound=self.tail_bound(a-1, cutoff))


def main():
    data = ROOT/'data'
    figures = ROOT/'figures'
    data.mkdir(exist_ok=True)
    figures.mkdir(exist_ok=True)
    rows = []
    constants = {}
    for q in (2, 3, 5):
        law = CriticalLaw(q)
        constants[str(q)] = {"g_infinity": mp.nstr(law.ginf, 60),
                             "omega": mp.nstr(law.odd, 60),
                             "c": mp.nstr(law.c, 60)}
        for a in range(-4, 9):
            rows.append(law.profile(a))
    # Repeat every displayed entry at higher precision and a larger cutoff.
    max_error = mp.mpf(0)
    for q in (2, 3, 5):
        high = CriticalLaw(q, precision=120, product_terms=600)
        for old in [r for r in rows if r['q'] == q]:
            new = high.profile(old['a'], cutoff=36)
            for name in ('mean', 'full_tv', 'dimension_tv', 'bayes_recovery',
                         'unique_nondegenerate', 'linear_recovery'):
                max_error = max(max_error, abs(old[name]-new[name]))
    assert max_error < mp.mpf('1e-70')
    with (data/'critical_profiles.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        for r in rows:
            writer.writerow({k: (v if isinstance(v, int) else mp.nstr(v, 45))
                             for k, v in r.items()})
    summary = {"method": "proved infinite-mixture formulas, truncated with explicit tail bounds",
               "constants": constants, "rows_checked": len(rows),
               "max_precision_recheck_error": mp.nstr(max_error, 8),
               "checks": ["normalization", "mean", "second factorial moment", "third factorial moment",
                          "strict full-vs-dimension advantage", "recovery ordering",
                          "a>=0 recovery identity", "higher-precision repeat"]}
    (data/'profile_validation.json').write_text(json.dumps(summary, indent=2)+'\n')

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(1, 2, figsize=(7, 3.9), constrained_layout=True)
    use = [r for r in rows if r['q'] == 2 and -3 <= r['a'] <= 5]
    x = [r['a'] for r in use]
    for field, label, color, marker in (
            ('full_tv', 'All observations', '#166a87', 'o'),
            ('dimension_tv', 'Candidate dimension only', '#b8672c', 's')):
        axes[0].plot(x, [float(r[field]) for r in use], marker=marker,
                     color=color, label=label, linewidth=1.8)
    for field, label, color, marker in (
            ('bayes_recovery', 'Optimal recovery (guess allowed)', '#166a87', 'o'),
            ('unique_nondegenerate', 'Unique nondegenerate candidate', '#55914e', '^'),
            ('linear_recovery', 'One-dimensional candidate space', '#b8672c', 's')):
        axes[1].plot(x, [float(r[field]) for r in use], marker=marker,
                     color=color, label=label, linewidth=1.8)
    for ax, title, ylabel in zip(axes,
            ['Testing the hidden-form model', 'Recovering the hidden form'],
            ['Total variation distance', 'Success probability']):
        ax.set(title=title, xlabel=r'Offset $a$ in $t=\binom{n}{2}-1+a$',
               ylabel=ylabel, ylim=(-.025, 1.025), xticks=x)
        ax.grid(axis='y', color='#dddddd', linewidth=.6)
        ax.legend(loc='lower right', fontsize=7.0, frameon=False)
    fig.suptitle('Critical limits over the binary field', fontsize=12)
    fig.savefig(figures/'critical_profiles.pdf')
    fig.savefig(figures/'critical_profiles.png', dpi=170)
    plt.close(fig)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
