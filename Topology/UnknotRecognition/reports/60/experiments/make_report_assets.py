#!/usr/bin/env python3
"""Generate article tables and exact data figures from the retained JSON files.

This is a reporting script, not a benchmark. It never alters measured data.
Run from the package root with matplotlib installed.
"""
import argparse
import json
import re
from pathlib import Path


def label(name):
    group, style, count = name.split('_')
    group = {'static': 'Static', 'meridian': 'Meridian', 'parallel': 'Parallel'}[group]
    return f'{group}, {style}, $r={count}$'


def table(path, header, rows, caption, table_label, spec='lrrrrr', size='small'):
    lines = [r'\begin{table}[htbp]', r'\centering' + chr(92) + size,
             r'\setlength{\tabcolsep}{4pt}',
             r'\begin{tabular}{@{}' + spec + r'@{}}', r'\toprule',
             ' & '.join(header) + r'\\', r'\midrule']
    lines += [' & '.join(row) + r'\\' for row in rows]
    lines += [r'\bottomrule', r'\end{tabular}', r'\caption{' + caption + '}',
              r'\label{' + table_label + '}', r'\end{table}', '']
    path.write_text('\n'.join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    results, article = root / 'results', root / 'article'
    primary = json.loads((results / 'geometry_benchmark.json').read_text())
    batched = json.loads((results / 'geometry_batched.json').read_text())
    rows = []
    for case in primary['results']:
        m, r = case['medians'], case['paired_ratios']
        rows.append([label(case['name'])] +
                    [f'{1000*m[arm]:.3f}' for arm in ('dense', 'sparse', 'sparse_verified')] +
                    [f'{r[arm]:.2f}' for arm in ('sparse', 'dense_control')])
    table(article / 'geometry_table.tex',
          ['Case', 'Dense', 'Sparse', 'Sparse + replay', 'D/S', 'A/A'], rows,
          'Final primary geometry experiment. Times are median milliseconds per complete call. '
          'D/S and A/A are medians of paired dense/sparse and dense/control ratios. '
          'The full JSON retains all four arms and all samples.', 'tab:geometry')

    rows = []
    for case in batched['results']:
        m, r = case['medians'], case['paired_ratios']
        rows.append([label(case['name']), str(case['batch'])] +
                    [f'{1000*m[arm]:.3f}' for arm in ('dense', 'sparse', 'sparse_verified')] +
                    [f'{r[arm]:.3f}' for arm in ('sparse', 'sparse_verified', 'dense_control')])
    table(article / 'batched_table.tex',
          ['Case', 'Batch', 'Dense', 'Sparse', 'Verified', 'D/S', 'D/V', 'A/A'], rows,
          'Batched follow-up: median milliseconds per call; seven paired rounds, '
          '4,704 measured calls and 672 excluded warm-up calls. D/V compares dense counting '
          'with sparse counting plus proof replay. The 0.945 ratio is a retained regression.',
          'tab:batched', spec='lrrrrrrr', size='footnotesize')

    capacities = [row for row in primary['capacity'] if 'exponent_bits' in row]
    rows = [[str(c['exponent_bits']), f"{1000*c['elapsed_seconds']:.2f}",
             f"{c['certificate_bytes']:,}", str(c['result']['distinct_vectors'])]
            for c in capacities]
    table(article / 'capacity_table.tex',
          ['$b$ in $K=2^b$', 'Produce + replay (ms)', 'Certificate bytes', 'Profiles'], rows,
          'Single completed capacity probes for $K d+(K+1)\\ell$ in an '
          'eight-tetrahedron solid torus. These are individual capacity observations, '
          'not repeated timing estimates or comparative speedup claims.',
          'tab:capacity', spec='rrrr')

    full_log = results / 'full_suite_complete.log'
    match = re.search(r'^Ran (\d+) tests in ([0-9.]+)s$', full_log.read_text(), re.M) if full_log.exists() else None
    passed = bool(match and re.search(r'^OK(?:\s|$)', full_log.read_text(), re.M))
    count = f'{int(match.group(1)):,}' if passed else r'\textit{pending final capture}'
    macros = [r'% Generated from retained results; do not edit measured JSON.',
              r'\newcommand{\FullTests}{' + count + '}',
              r'\newcommand{\LargestCertificateBytes}{' + f"{max(c['certificate_bytes'] for c in capacities):,}" + '}', '']
    (article / 'generated_numbers.tex').write_text('\n'.join(macros))

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.grid': True, 'grid.alpha': 0.20,
                         'pdf.fonttype': 42, 'ps.fonttype': 42,
                         'savefig.bbox': 'tight'})
    figures = article / 'figures'
    figures.mkdir(exist_ok=True)
    fig, axes = plt.subplots(1, 2, figsize=(6.6, 3.1))
    styles = [('dense', 'Dense', '#8b3933', 'o'),
              ('dense_control', 'Dense control', '#a9a29d', 'x'),
              ('sparse', 'Sparse', '#126879', 's'),
              ('sparse_verified', 'Sparse + replay', '#405495', '^')]
    for ax, group, counts, title in zip(axes, ['static', 'parallel'], [(4, 8, 12), (4, 6, 8)],
                                      ['Static disjoint ports', r'Parallel meridians ($2^{64}$ copies)']):
        byname = {case['name']: case for case in primary['results']}
        for arm, legend, colour, marker in styles:
            y = [1000 * byname[f'{group}_disjoint_{r}']['medians'][arm] for r in counts]
            ax.plot(counts, y, marker=marker, markersize=4, linewidth=1.3,
                    color=colour, label=legend)
        ax.set_yscale('log')
        ax.set_xticks(counts)
        ax.set_xlabel('Number of supplied ports')
        ax.set_title(title, fontsize=9)
    axes[0].set_ylabel('Median complete-call time (ms)')
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='lower center', ncol=4, frameon=False,
               bbox_to_anchor=(0.51, -0.03), fontsize=8)
    fig.tight_layout(rect=(0, 0.08, 1, 1))
    fig.savefig(figures / 'geometry_scaling.pdf')
    fig.savefig(figures / 'geometry_scaling.png', dpi=180)
    plt.close(fig)

    # The sharpness figure is an exact seven-point transfer, not an image model.
    fig, axes = plt.subplots(2, 1, figsize=(5.5, 2.5), sharex=True)
    for ax, values, title in zip(axes, [[1]*7, [1, 2, 2, 1, 1, 0]],
                                 ['Before transfer: one run', 'After transfer and truncation: four runs']):
        ax.bar(range(len(values)), values, width=0.88, color='#126879')
        ax.set_ylim(-0.15, 2.6)
        ax.set_yticks([0, 1, 2])
        ax.set_title(title, fontsize=9)
        ax.set_ylabel('Weight')
        ax.grid(axis='x', visible=False)
    axes[1].axvspan(5.5, 6.5, color='#cccccc', alpha=0.5)
    axes[1].text(6, 1.2, 'removed', ha='center', rotation=90, fontsize=8)
    axes[1].set_xticks(range(7))
    axes[1].set_xlabel('Integer point')
    fig.tight_layout()
    fig.savefig(figures / 'sharp_transfer.pdf')
    fig.savefig(figures / 'sharp_transfer.png', dpi=180)
    plt.close(fig)
    print(json.dumps({'tables': 3, 'figures': 2, 'full_suite_summary_found': passed,
                      'full_test_count': int(match.group(1)) if passed else None}))


if __name__ == '__main__':
    main()
