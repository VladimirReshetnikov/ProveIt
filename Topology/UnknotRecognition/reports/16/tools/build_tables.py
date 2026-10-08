#!/usr/bin/env python3
"""Regenerate the article's exact tables and static figure from archived JSON.

Run from any directory. Figure generation needs matplotlib; --tables-only uses
only Python's standard library. This does not rerun any benchmark.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

BUNDLE = Path(__file__).resolve().parents[1]
NAMES = {
    'trefoil': 'Trefoil', 'figure_eight': 'Figure eight',
    'conway': 'Conway', 'kinoshita_terasaka': 'Kinoshita--Terasaka',
    'hard_unknot_8': 'Hard unknot 8', 'torus_3_5': '$T(3,5)$',
    'torus_3_7': '$T(3,7)$', 'hard_unknot_27': 'Generated hard unknot 27',
    'stress_braid5_36': 'Stress braid5 36',
}


def read(path):
    return json.loads((BUNDLE / path).read_text())


def tabular(spec, header, rows):
    lines = ['% Generated from archived measurements; do not edit by hand.',
             r'\begin{tabular}{' + spec + '}', r'\toprule',
             ' & '.join(header) + r' \\', r'\midrule']
    lines.extend(' & '.join(map(str, row)) + r' \\' for row in rows)
    lines.extend([r'\bottomrule', r'\end{tabular}', ''])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tables-only', action='store_true')
    args = parser.parse_args()
    target = BUNDLE / 'article/generated'
    target.mkdir(parents=True, exist_ok=True)
    dense = read('verification/algebra/dense_benchmarks_final.json')['records']
    rows = []
    for item in dense:
        med = item['median_seconds']
        rows.append([item['arcs'], f"{item['left_terms']} / {item['right_terms']}",
                     *(f'{1000 * med[x]:.3f}' for x in ('baseline', 'adaptive', 'dense')),
                     f"{item['speedup_adaptive']:.2f}"])
    (target / 'dense_table.tex').write_text(tabular(
        'rrrrrr', ['$m$', 'Input supports', 'Baseline', 'Adaptive', 'Dense', 'Ratio'], rows))

    scanners = read('implementation/fast/paired_scanner_benchmark.json')['fixtures']
    rows = []
    for item in scanners:
        rows.append([NAMES[item['name']], item['crossings'],
                     *(f"{1000 * item['summary'][x]['median_seconds']:.3f}"
                       for x in ('legacy', 'adaptive', 'dense'))])
    (target / 'scanner_table.tex').write_text(tabular(
        'lrrrr', ['Fixture', '$n$', 'Legacy', 'Adaptive', 'Dense'], rows))

    quotients = read('verification/finite_quotient/finite_quotient_benchmark.json')['fixtures']
    rows = []
    for item in quotients:
        tests = item['measurements']
        seed = tests['a5_seed']
        label = NAMES[item['name']] + (r'$\dagger$' if seed['status'] != 'KNOTTED' else '')
        kh = tests.get('existing_khovanov_raw')
        rows.append([label, len(item['seeds']), seed['assignments'],
                     f"{1000 * seed['median_seconds']:.3f}",
                     f"{1000 * tests['existing_default']['median_seconds']:.3f}",
                     f"{1000 * kh['median_seconds']:.3f}" if kh else '---'])
    (target / 'quotient_table.tex').write_text(tabular(
        'lrrrrr', ['Fixture', '$b$', '$a$', '$A_5$ seeds', 'Default', 'Raw Kh'], rows))

    if not args.tables_only:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        plt.rcParams.update({'font.size': 10, 'axes.spines.top': False,
                             'axes.spines.right': False, 'pdf.fonttype': 42})
        fig, ax = plt.subplots(figsize=(7.0, 3.7), constrained_layout=True)
        sizes = [r['arcs'] for r in dense]
        for key, label, color in [('baseline', 'Baseline pair loop', '#b25924'),
                                  ('adaptive', 'Adaptive factorization', '#145b91'),
                                  ('dense', 'Forced dense', '#188279')]:
            med = [1000 * r['median_seconds'][key] for r in dense]
            lo = [1000 * min(x['seconds'] for x in r['samples'][key]) for r in dense]
            hi = [1000 * max(x['seconds'] for x in r['samples'][key]) for r in dense]
            ax.fill_between(sizes, lo, hi, alpha=.10, color=color, linewidth=0)
            ax.plot(sizes, med, 'o-', label=label, color=color, markersize=4, linewidth=1.7)
        ax.set_yscale('log')
        ax.set_xticks(sizes)
        ax.set_xlabel(r'Arcs $m$ (frontier has $2m$ endpoints)')
        ax.set_ylabel('Cold composition time (ms; log scale)')
        ax.set_title('Arbitrary coefficient tables in the squarefree algebra', loc='left', pad=10)
        ax.grid(axis='y', which='major', alpha=.18)
        ax.legend(frameon=False, loc='upper left')
        out = BUNDLE / 'article/figures'
        out.mkdir(parents=True, exist_ok=True)
        fig.savefig(out / 'composition_times.pdf', metadata={'Title': 'Cold composition benchmark',
                                                           'Creator': 'tools/build_tables.py'})
        fig.savefig(out / 'composition_times.png', dpi=180)
        plt.close(fig)
    print('Generated three TeX tables' + (' and the static figure.' if not args.tables_only else '.'))


if __name__ == '__main__':
    main()
