#!/usr/bin/env python3
"""Render the manuscript's numerical tables and vector figures from raw results."""
import argparse
import json
from pathlib import Path


def table(path, caption, label, columns, headers, rows, note=None):
    lines = [r'\begin{table}[htbp]', r'\centering', r'\small',
             r'\begin{tabular}{' + columns + '}', r'\toprule',
             ' & '.join(headers) + r' \\', r'\midrule']
    lines.extend(' & '.join(map(str, row)) + r' \\' for row in rows)
    lines.extend([r'\bottomrule', r'\end{tabular}',
                  r'\caption{' + caption + '}', r'\label{' + label + '}'])
    if note:
        lines.append(r'\par\smallskip\footnotesize ' + note)
    lines.append(r'\end{table}')
    path.write_text('\n'.join(lines) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, required=True)
    parser.add_argument('--article', type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.results.read_text())
    tab = args.article / 'tables'
    fig = args.article / 'figures'
    tab.mkdir(parents=True, exist_ok=True)
    fig.mkdir(parents=True, exist_ok=True)
    by_family = {}
    for result in data['summaries']:
        by_family.setdefault(result['family'], []).append(result)
    ms = lambda result, arm: f"{result['medians'][arm] * 1000:.3f}"
    speed = lambda result: f"{result['median_paired_speedup']['adaptive']:.2f}"

    table(tab / 'five_cycle.tex',
          'Complete five-cycle counts: exact merger tests and median elapsed times.',
          'tab:five-cycle', 'rrrrrrr',
          ['$k$', 'Old tests', 'Queue tests', 'Old ms', 'Adaptive ms',
           'Queue ms', 'Paired gain'],
          [[r['pairings'], f"{r['pair_tests']['baseline']:,}",
            f"{r['pair_tests']['queue']:,}", ms(r, 'baseline'),
            ms(r, 'adaptive'), ms(r, 'queue'), speed(r)]
           for r in by_family['five-cycle']],
          'Paired gain is the median of the seven old/adaptive time ratios; '
          'it need not equal the ratio of the two medians. All cases have five cycles.')
    table(tab / 'easy_duplicates.tex',
          'Easy duplicate inputs. All adaptive runs complete without a queue switch.',
          'tab:easy', 'rrrrrr',
          ['$k$', 'Tests: old/adaptive', 'Old ms', 'Adaptive ms', 'Queue ms',
           'Paired gain'],
          [[r['pairings'], r['pair_tests']['baseline'], ms(r, 'baseline'),
            ms(r, 'adaptive'), ms(r, 'queue'), speed(r)]
           for r in by_family['easy-duplicates']])
    table(tab / 'native_meridians.tex',
          'Complete interval counts on native layered-solid-torus meridian arc systems.',
          'tab:native', 'rrrrrrr',
          ['$t$', '$k$', 'Bits of $N$', 'Cycles', 'Old ms', 'Adaptive ms',
           'Paired gain'],
          [[r['parameter'], r['pairings'], r['universe_bits'], r['cycles'],
            ms(r, 'baseline'), ms(r, 'adaptive'), speed(r)]
           for r in by_family['normal-meridian']],
          'Geometry is constructed before timing. There are no adaptive queue '
          'switches and no changes in merger-test count in these cases.')
    table(tab / 'binary_size.tex',
          'Fixed 32-pairing, five-cycle instances with increasing endpoint bit length.',
          'tab:binary', 'rrrrr',
          ['Bits of $N$', 'Old ms', 'Adaptive ms', 'Queue ms', 'Paired gain'],
          [[r['universe_bits'], ms(r, 'baseline'), ms(r, 'adaptive'),
            ms(r, 'queue'), speed(r)]
           for r in by_family['binary-size']])
    table(tab / 'profile_costs.tex',
          'Native query costs, including fresh geometry validation. The outputs differ.',
          'tab:profile-costs', 'rrr',
          ['$t$', 'Aggregate topology ms', 'Component profile ms'],
          [[r['tetrahedra'], f"{r['medians']['aggregate_topology']*1000:.3f}",
            f"{r['medians']['component_profile']*1000:.3f}"]
           for r in data['topology_summaries']],
          'These are costs of two different interfaces, not a same-task speedup experiment.')

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.titleweight': 'bold', 'axes.labelcolor': '#17324D',
                         'pdf.fonttype': 42, 'ps.fonttype': 42})
    colors = {'baseline': '#17324D', 'adaptive': '#16817A', 'queue': '#B96927'}
    names = {'baseline': 'Pinned baseline', 'adaptive': 'Adaptive', 'queue': 'Eager queue'}
    markers = {'baseline': 'o', 'adaptive': 's', 'queue': '^'}

    def plot_panel(ax, family, field, title, xlabel, ylabel):
        rows = by_family[family]
        x = [r['pairings'] if family != 'normal-meridian' else r['parameter']
             for r in rows]
        for arm in ('baseline', 'adaptive', 'queue'):
            y = [r[field][arm] * (1000 if field == 'medians' else 1) for r in rows]
            ax.loglog(x, y, marker=markers[arm], color=colors[arm],
                      label=names[arm], linewidth=1.8, markersize=4)
        ax.set(title=title, xlabel=xlabel, ylabel=ylabel)
        ax.set_xticks(x, [str(n) for n in x])
        ax.grid(True, which='major', color='#DFE5E9', linewidth=0.6)
        ax.legend(frameon=False, fontsize=8)

    f, axes = plt.subplots(1, 2, figsize=(7.1, 3.0), constrained_layout=True)
    plot_panel(axes[0], 'five-cycle', 'pair_tests',
               'Exact merger work', 'Initial pairings k', 'Merger tests')
    plot_panel(axes[1], 'five-cycle', 'medians',
               'Complete five-cycle counts', 'Initial pairings k', 'Median time (ms)')
    for suffix in ('pdf', 'png'):
        f.savefig(fig / ('five_cycle.' + suffix), dpi=200)
    plt.close(f)
    f, axes = plt.subplots(1, 2, figsize=(7.1, 3.0), constrained_layout=True)
    plot_panel(axes[0], 'easy-duplicates', 'medians',
               'Easy duplicate inputs', 'Initial pairings k', 'Median time (ms)')
    plot_panel(axes[1], 'normal-meridian', 'medians',
               'Native meridian systems', 'Tetrahedra t', 'Median time (ms)')
    for suffix in ('pdf', 'png'):
        f.savefig(fig / ('easy_and_native.' + suffix), dpi=200)
    plt.close(f)
    print(json.dumps({'tables': 5, 'figures': 2, 'raw_samples': len(data['samples']),
                      'topology_samples': len(data['topology_samples'])}))


if __name__ == '__main__':
    main()
