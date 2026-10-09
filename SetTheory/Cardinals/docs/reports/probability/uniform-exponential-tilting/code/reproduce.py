#!/usr/bin/env python3
"""Reproduce the research article's tests, certified examples, tables, and figure.

All reported probability intervals come from actual Arb/Acb calculations.
The plots show counts of Fourier residues, not inferred elapsed-time speedups.
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import time
import unittest

import flint
from flint import arb, ctx, fmpq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

from certified_coefficients import certify_probability, certify_coefficient, interval_to_arb
import test_certified_coefficients

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'
FIGURES = ROOT / 'figures'


def midpoint_string(interval, digits=20):
    with ctx.workprec(512):
        return interval_to_arb(interval).mid().str(digits, radius=False)


def mid_float(interval):
    with ctx.workprec(512):
        return float(interval_to_arb(interval).mid())


def contains_binomial_reference(result, n, k, p):
    with ctx.workprec(max(400, n.bit_length() + 256)):
        pball = arb(fmpq(p.numerator, p.denominator))
        reference = (arb(n + 1).lgamma() - arb(k + 1).lgamma()
                     - arb(n - k + 1).lgamma()
                     + k * pball.log() + (n - k) * (1 - pball).log())
        lo = result['log_probability']['lower']
        hi = result['log_probability']['upper']
        lower = arb((int(lo['mantissa']), int(lo['exponent'])))
        upper = arb((int(hi['mantissa']), int(hi['exponent'])))
        assert lower <= reference.lower() and reference.upper() <= upper
        marginal = result['conditional_marginals'][0]
        mlo, mhi = marginal['lower'], marginal['upper']
        lower_m = arb((int(mlo['mantissa']), int(mlo['exponent'])))
        upper_m = arb((int(mhi['mantissa']), int(mhi['exponent'])))
        exact = arb(fmpq(k, n))
        assert lower_m <= exact.lower() and exact.upper() <= upper_m
        return {'independent_loggamma_reference': reference.str(35),
                'reference_contained': True,
                'exact_representative_marginal': str(Fraction(k, n))}


def write_csv(path, rows):
    with path.open('w', newline='') as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def scientific_tex(value, digits=6):
    if value == 0:
        return '$0$'
    if abs(value) < 1e5 and abs(value) >= 1e-3:
        return f'${value:.{digits}g}$'
    mantissa, exponent = f'{value:.{digits-1}e}'.split('e')
    return f'${mantissa}\\times10^{{{int(exponent)}}}$'


def run_examples():
    examples = [
        ('central_million', ['1/2'], [10**6], 500000),
        ('central_trillion', ['1/2'], [10**12], 5*10**11),
        ('rare_trillion', ['1/1000000'], [10**12], 10**9),
        ('nearly_deterministic', ['1/1000000000000', '999999999999/1000000000000'], [60, 20], 20),
        ('heterogeneous_256', [str(Fraction((37*i) % 257, 257)) for i in range(1,257)], [1]*256, 200),
    ]
    rows, full = [], []
    for name, p, multiplicities, k in examples:
        started = time.perf_counter()
        result = certify_probability(p, k, '1e-12', multiplicities=multiplicities, marginals=True)
        elapsed = time.perf_counter() - started
        record = {'name': name, 'input': {'probabilities': p, 'multiplicities': multiplicities, 'k':k},
                  'result':result, 'runtime_seconds':elapsed}
        if len(p) == 1:
            record['independent_check'] = contains_binomial_reference(result, sum(multiplicities), k, Fraction(p[0]))
        rows.append({'name':name, 'degree':sum(multiplicities), 'groups':len(p), 'target':k,
                     'log_probability_midpoint':midpoint_string(result['log_probability'], 24),
                     'grid_size':result['stats']['grid_size'], 'retained_nodes':result['stats']['node_count'],
                     'complex_evaluations':result['stats']['complex_evaluations'],
                     'precision_bits':result['stats']['precision_bits'],
                     'tilt_evaluations':result['stats']['tilt_evaluations'],
                     'relative_interval_width_display':mid_float(result['certificate']['relative_width_bound']),
                     'runtime_seconds':elapsed})
        full.append(record)
        print(f"{name}: N={sum(multiplicities)}, nodes={result['stats']['node_count']}, bits={result['stats']['precision_bits']}", flush=True)
    polynomial = certify_coefficient([['2','3'],['5/7','11/13']], 80, '1e-12', multiplicities=[50,75], marginals=True)
    full.append({'name':'positive_polynomial', 'input':{'factors':[['2','3'],['5/7','11/13']], 'k':80,'multiplicities':[50,75]},'result':polynomial})
    (RESULTS/'coefficient_examples.json').write_text(json.dumps(full,indent=2)+'\n')
    write_csv(RESULTS/'coefficient_examples.csv',rows)
    title = {'central_million':'Central binomial', 'central_trillion':'Central binomial',
             'rare_trillion':'Rare binomial', 'nearly_deterministic':'Almost deterministic',
             'heterogeneous_256':'Heterogeneous'}
    lines = [r'\begin{table}[H]',r'\centering\small',r'\begin{tabular}{@{}lrrrrr@{}}',r'\toprule',
             r'Example & Degree $N$ & Groups & $\log p_k$ & Nodes & Bits \\',r'\midrule']
    for row in rows:
        degree = str(row['degree']) if row['degree'] < 10**5 else '$10^{'+str(round(math.log10(row['degree'])))+'}$'
        lines.append(f"{title[row['name']]} & {degree} & {row['groups']} & {scientific_tex(float(row['log_probability_midpoint']))} & {row['retained_nodes']} & {row['precision_bits']} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Certified coefficient examples at requested relative tolerance $10^{-12}$. The displayed logarithms are rounded summaries; exact interval endpoints are supplied in the JSON results. All requested representative marginal intervals also passed their width checks.}',r'\label{tab:coefficientexamples}',r'\end{table}']
    (RESULTS/'coefficient_examples.tex').write_text('\n'.join(lines)+'\n')
    return rows


def run_scaling():
    degree_rows = []
    for exponent in range(2,31,2):
        n = 10**exponent
        result = certify_probability(['1/2'], n//2, '1e-12', multiplicities=[n])
        degree_rows.append({'degree':n, 'log10_degree':exponent, 'grid_size':result['stats']['grid_size'],
                            'retained_nodes':result['stats']['node_count'], 'precision_bits':result['stats']['precision_bits']})
    precision_rows = []
    for digits in (3,6,12,24,48):
        n=10**12
        result = certify_probability(['1/2'], n//2, f'1e-{digits}', multiplicities=[n])
        precision_rows.append({'tolerance_digits':digits,'degree':n,'grid_size':result['stats']['grid_size'],
                               'retained_nodes':result['stats']['node_count'],'precision_bits':result['stats']['precision_bits']})
    write_csv(RESULTS/'frequency_scaling.csv',degree_rows)
    write_csv(RESULTS/'accuracy_scaling.csv',precision_rows)
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                         'axes.labelcolor':'#16324F','text.color':'#16324F','axes.titleweight':'bold'})
    fig, axes = plt.subplots(1,2,figsize=(10,3.7), layout='constrained')
    ax=axes[0]
    xs=[r['log10_degree'] for r in degree_rows]
    ax.plot(xs,[r['grid_size'] for r in degree_rows],color='#9AA9B8',marker='o',label='Full grid modulus M')
    ax.plot(xs,[r['retained_nodes'] for r in degree_rows],color='#087E8B',marker='s',label='Retained residues')
    ax.set_yscale('log');ax.set_xlabel(r'Encoded degree: $\log_{10}N$');ax.set_ylabel('Number of Fourier residues')
    ax.set_title(r'Fixed relative tolerance $10^{-12}$',loc='left',pad=12)
    ax.legend(frameon=False,loc='upper left',fontsize=8);ax.grid(axis='y',alpha=.15)
    ax=axes[1]
    ax.plot([r['tolerance_digits'] for r in precision_rows],[r['retained_nodes'] for r in precision_rows],color='#087E8B',marker='o')
    ax.set_xlabel(r'Requested digits: $-\log_{10}\varepsilon$');ax.set_ylabel('Retained Fourier residues')
    ax.set_title(r'Fixed degree $N=10^{12}$',loc='left',pad=12)
    ax.grid(axis='y',alpha=.15)
    fig.savefig(FIGURES/'frequency_scaling.pdf')
    fig.savefig(FIGURES/'frequency_scaling.png',dpi=180)
    plt.close(fig)


def sampling_table():
    rows = list(csv.DictReader((RESULTS/'sampling_examples.csv').open()))
    selected = [r for r in rows if r['name'] in ('binary_center_100','equal_large_center_100','equal_large_skew_100','dominant_capacity','heterogeneous_skew')]
    title = {'binary_center_100':'100 binary columns','equal_large_center_100':'100 capacities of 1000',
             'equal_large_skew_100':'100 capacities of 1000','dominant_capacity':'One dominant capacity',
             'heterogeneous_skew':r'Capacities $1,2,4,\ldots,128$'}
    lines=[r'\begin{table}[H]',r'\centering\small',r'\begin{tabular}{@{}lrrr@{}}',r'\toprule',
           r'Capacities & First-row sum & Acceptance & Expected proposals \\',r'\midrule']
    for row in selected:
        lines.append(f"{title[row['name']]} & {int(row['target']):,} & {float(row['acceptance']):.6g} & {float(row['expected_trials']):.6g} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}',
              r'\caption{Acceptance probabilities computed by exact rational formulas, with rounded decimal displays. The skew example with 100 capacities uses $q=1/2$; its uniform-coordinate counterpart has acceptance approximately $10^{-238.387}$. The selected tilt gives about $17.75$ expected proposals.}',r'\label{tab:samplingexamples}',r'\end{table}']
    (RESULTS/'sampling_examples.tex').write_text('\n'.join(lines)+'\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-tests',action='store_true',help='Regenerate examples and tables from previously verified code.')
    args=parser.parse_args()
    RESULTS.mkdir(exist_ok=True);FIGURES.mkdir(exist_ok=True)
    if not args.skip_tests:
        suite=unittest.defaultTestLoader.loadTestsFromModule(test_certified_coefficients)
        with (RESULTS/'coefficient_tests.txt').open('w') as stream:
            result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
        if not result.wasSuccessful():
            raise SystemExit('Coefficient test failure; see results/coefficient_tests.txt')
        test_summary={'test_methods':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'successful':True}
        subprocess.run([sys.executable,str(ROOT/'code'/'sampling_checks.py'),'--output',str(RESULTS)],check=True,stdout=subprocess.DEVNULL)
    else:
        saved_summary_path=RESULTS/'validation_summary.json'
        if not saved_summary_path.exists():
            raise SystemExit('--skip-tests requires a previously recorded validation_summary.json.')
        test_summary=json.loads(saved_summary_path.read_text())['coefficient_tests']
        if not test_summary.get('successful'):
            raise SystemExit('Previously recorded tests did not succeed.')
        test_summary['test_log_reused']=True
    rows=run_examples();run_scaling();sampling_table()
    sampling=json.loads((RESULTS/'sampling_checks.json').read_text())
    summary={'coefficient_tests':test_summary,
             'sampling_uniform_enumerations':len(sampling['uniform_distribution_checks']),
             'sampling_exact_modal_variance_cases':sampling['modal_variance_checks']['exact_rational_cases'],
             'sampling_arbitrary_margin_cases':sampling['arbitrary_margin_bound_checks']['cases'],
             'sampling_reference_draws':sampling['seeded_reference_sampling']['samples'],
             'coefficient_examples':len(rows),
             'python':platform.python_version(),'python_flint':flint.__version__,
             'note':'Timings are environment-specific observations; no production runtime comparison is claimed.'}
    (RESULTS/'validation_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    methods=test_summary['test_methods']
    (RESULTS/'validation_summary.tex').write_text(
        '\\paragraph{Recorded validation.} '
        f"The coefficient test suite passed {methods} test methods, covering exact rational coefficient and marginal comparisons, extreme probabilities, deterministic inputs, precision adaptation, and independently checked compressed binomials. "
        f"The sampling checker passed {summary['sampling_uniform_enumerations']} exhaustively enumerated conditional laws, {summary['sampling_exact_modal_variance_cases']} exact modal-variance cases, and {summary['sampling_arbitrary_margin_cases']} arbitrary-margin rational-tilt bound checks. "
        f"All {summary['sampling_reference_draws']} seeded reference samples were feasible; their histogram is not used as a uniformity proof. The recorded runtime used Python {platform.python_version()} and python-flint {flint.__version__}.\n")
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':
    main()
