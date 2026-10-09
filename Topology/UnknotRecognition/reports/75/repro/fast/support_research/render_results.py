#!/usr/bin/env python3
"""Render paper figures and exact LaTeX tables from one retained benchmark.

No benchmark or new measurements are performed. Main plots show every timed
A-arm sample and connect its observed medians; there is no fitted trend.
The companion CSV retains the underlying integer nanosecond measurements.

Example from a delivered package root::

    python repo_overlay/Topology/UnknotRecognition/fast/support_research/render_results.py \
        --article-dir article
"""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import statistics

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, NullLocator


BLUE = '#285B8C'
TEAL = '#168374'
ORANGE = '#C76A3B'


def samples(document, cohort, arm):
    return [row for row in document['samples'] if row['cohort'] == cohort
            and row['arm'] == arm and not row['warmup'] and row['status'] == 'COMPLETE']


def median(document, cohort, arm, field='total_ns'):
    rows = samples(document, cohort, arm)
    if not rows:
        raise ValueError('missing complete measured samples: ' + cohort + ' / ' + arm)
    return statistics.median(row[field] for row in rows)


def comparison(document, cohort, numerator, denominator):
    matches = [row for row in document['summaries'] if row['cohort'] == cohort
               and row['numerator_arm'] == numerator and row['denominator_arm'] == denominator]
    if len(matches) != 1 or not matches[0]['reported']:
        raise ValueError('missing complete planned comparison: ' + cohort)
    return matches[0]


def ms(value):
    return f'{value / 1e6:.3f}'


def ratio(row):
    return f"{row['paired_total_ratio_median']:.3f}"


def fibonacci_cohorts(document, category):
    return sorted((row for row in document['cohorts']
                   if row.get('family') == 'fibonacci' and row.get('category') == category
                   and row['status'] == 'COMPLETE'), key=lambda row: row['tetrahedra'])


def style_axes(axis, ticks, ylabel=None):
    axis.set_xscale('log', base=2)
    axis.set_yscale('log', base=10)
    axis.set_xticks(ticks, [str(value) for value in ticks])
    axis.xaxis.set_minor_locator(NullLocator())
    axis.grid(axis='both', which='major', color='#E0E5E8', linewidth=0.6)
    axis.set_axisbelow(True)
    axis.spines['top'].set_visible(False)
    axis.spines['right'].set_visible(False)
    axis.tick_params(length=3, width=0.7)
    axis.set_xlabel(r'Tetrahedra $t$ (base-2 log)')
    if ylabel:
        axis.set_ylabel(ylabel)


def plot_times(axis, document, cohorts, arm, label, color, marker='o'):
    xs, ys = [], []
    for cohort in cohorts:
        rows = samples(document, cohort['id'], arm)
        t = cohort['tetrahedra']
        values = [row['total_ns'] / 1e6 for row in rows]
        axis.scatter([t] * len(values), values, s=10, color=color,
                     alpha=0.30, linewidths=0, zorder=2)
        xs.append(t)
        ys.append(statistics.median(values))
    axis.plot(xs, ys, color=color, linewidth=1.45, marker=marker,
              markersize=4.2, label=label, zorder=3)
    return xs, ys


def save_figure(figure, target):
    figure.savefig(target.with_suffix('.pdf'), bbox_inches='tight',
                   metadata={'Creator': 'support_research/render_results.py',
                             'CreationDate': None, 'ModDate': None})
    figure.savefig(target.with_suffix('.png'), dpi=240, bbox_inches='tight')
    plt.close(figure)


def render_figures(document, article_dir):
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 8.7,
        'axes.titlesize': 9.5, 'axes.labelsize': 8.3, 'xtick.labelsize': 8.0,
        'ytick.labelsize': 8.0, 'legend.fontsize': 7.9, 'axes.edgecolor': '#83909A',
        'axes.linewidth': 0.7, 'pdf.fonttype': 42, 'ps.fonttype': 42,
        'mathtext.fontset': 'dejavusans', 'savefig.facecolor': 'white'})
    disc = fibonacci_cohorts(document, 'discs')
    coordinates = fibonacci_cohorts(document, 'coordinates')
    capacity = fibonacci_cohorts(document, 'ray_capacity')
    figure, axes = plt.subplots(1, 2, figsize=(6.3, 4.0))
    figure.subplots_adjust(left=0.095, right=0.985, bottom=0.28, top=0.89, wspace=0.32)
    a, b = axes
    disc_ticks = [row['tetrahedra'] for row in disc + capacity]
    coordinate_ticks = [row['tetrahedra'] for row in coordinates]
    style_axes(a, disc_ticks, 'Generation + external replay (ms)')
    style_axes(b, coordinate_ticks)
    a.set_title('(a) Essential-disc count', loc='left', pad=10)
    b.set_title('(b) Full coordinate census', loc='left', pad=10)
    plot_times(a, document, disc, 'old_disc_A', 'Maintained disc kernel', BLUE)
    plot_times(a, document, disc, 'ray_disc_A', 'Unit-peeling ray', TEAL)
    for cohort in capacity:
        rows = samples(document, cohort['id'], 'ray_disc_A')
        values = [row['total_ns'] / 1e6 for row in rows]
        a.scatter([cohort['tetrahedra']] * len(values), values, s=12, color=TEAL,
                  alpha=0.30, linewidths=0, zorder=2)
        a.plot([cohort['tetrahedra']], [statistics.median(values)], marker='D',
               color=TEAL, markerfacecolor='white', markeredgewidth=1.2,
               markersize=5.5, linestyle='none', label='Ray-only capacity', zorder=4)
    xs, old = plot_times(b, document, coordinates, 'old_compact_A', 'Maintained compact', BLUE)
    _, new = plot_times(b, document, coordinates, 'support_packed_A', 'Compiled + packed', ORANGE)
    b.fill_between(xs, old, new, where=[y >= x for x, y in zip(old, new)],
                   color=ORANGE, alpha=0.10, linewidth=0, zorder=1)
    a.set_ylim(1.6, 2600)
    b.set_ylim(1.6, 2600)
    a.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f'{value:g}'))
    b.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f'{value:g}'))
    a.legend(loc='upper left', frameon=False, borderaxespad=0.05, handlelength=1.5)
    b.legend(loc='upper left', frameon=False, borderaxespad=0.05, handlelength=1.5)
    figure.text(0.095, 0.030,
        'Faint points: measured A-arm calls. Lines: observed medians; no trend fit.\n'
        'Five paired rounds through t = 128; three at t = 256 and for capacity.\n'
        'Orange shading marks the measured full-census regression.',
        fontsize=7.7, color='#47545E', va='bottom')
    save_figure(figure, article_dir / 'benchmarks')

    figure, axis = plt.subplots(figsize=(6.3, 2.8))
    figure.subplots_adjust(left=0.12, right=0.98, bottom=0.24, top=0.89)
    style_axes(axis, disc_ticks, 'Certificate JSON bytes')
    axis.set_title('Essential-disc certificates: retained exact sizes', loc='left', pad=9)
    for arm, label, color in (('old_disc_A', 'Maintained disc kernel', BLUE),
                               ('ray_disc_A', 'Unit-peeling ray', TEAL)):
        points = [(row['tetrahedra'], median(document, row['id'], arm, 'certificate_json_bytes'))
                  for row in disc]
        axis.plot([x for x, _ in points], [y for _, y in points], color=color,
                  marker='o', markersize=4.3, linewidth=1.4, label=label)
    for cohort in capacity:
        axis.plot([cohort['tetrahedra']],
                  [median(document, cohort['id'], 'ray_disc_A', 'certificate_json_bytes')],
                  color=TEAL, marker='D', markerfacecolor='white', markeredgewidth=1.2,
                  markersize=5.5, linestyle='none', label='Ray-only capacity')
    axis.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f'{int(value):,}'))
    axis.legend(loc='upper left', frameon=False, borderaxespad=0.15, handlelength=1.8)
    save_figure(figure, article_dir / 'proof_sizes')


def table(caption, label, columns, heading, rows):
    return '\n'.join([
        r'\begin{table}[tbp]', r'\centering\small',
        r'\setlength{\tabcolsep}{4.5pt}', '\\caption{' + caption + '}',
        '\\label{' + label + '}', '\\begin{tabular}{' + columns + '}',
        r'\toprule', heading + r' \\', r'\midrule',
        *rows, r'\bottomrule', r'\end{tabular}', r'\end{table}', ''])


def render_tables(document, article_dir):
    parts = [
        '% Automatically generated from the retained benchmark; do not hand-edit numerical rows.',
        r'Table entries are separate medians in milliseconds. Each ratio is the median',
        r'of the first time divided by the second time within the same measured round;',
        r'it need not equal the ratio of the two displayed medians. Warm-ups are excluded.',
        '']
    rows = []
    for cohort in fibonacci_cohorts(document, 'discs'):
        item = comparison(document, cohort['id'], 'old_disc_A', 'ray_disc_A')
        rows.append(' & '.join([str(cohort['tetrahedra']), str(item['complete_pairs']),
            ms(item['numerator_total_ns_median']), ms(item['denominator_total_ns_median']),
            ratio(item)]) + r' \\')
    for cohort in fibonacci_cohorts(document, 'ray_capacity'):
        count = len(samples(document, cohort['id'], 'ray_disc_A'))
        rows.append(' & '.join([str(cohort['tetrahedra']), str(count), '---',
            ms(median(document, cohort['id'], 'ray_disc_A')), '---']) + r' \\')
    parts.append(table(
        r'Fibonacci meridian disc counts. Both methods include fresh generation and one '
        r'external replay; the ray producer also performs its existing internal replay. '
        r'The 512-tetrahedron entry is a ray-only capacity measurement, with no baseline ratio.',
        'tab:raytimes', 'rrrrr',
        r'$t$ & Pairs/calls & Old disc (ms) & Ray disc (ms) & Old/ray', rows))
    rows = []
    for cohort in fibonacci_cohorts(document, 'coordinates'):
        item = comparison(document, cohort['id'], 'old_compact_A', 'support_packed_A')
        first = samples(document, cohort['id'], 'old_compact_A')[0]
        packed = samples(document, cohort['id'], 'support_packed_A')[0]
        rows.append(' & '.join([str(cohort['tetrahedra']), str(first['weight_dimension']),
            str(packed['projection_dimension']), ms(item['numerator_total_ns_median']),
            ms(median(document, cohort['id'], 'support_vector_A')),
            ms(item['denominator_total_ns_median']), ratio(item)]) + r' \\')
    parts.append(table(
        r'Complete coordinate censuses on the same Fibonacci sources: dimension reduction '
        r'does not compensate for general rank-compilation overhead in this experiment. '
        r'The old implementation already uses its single-orbit shortcut. There are five '
        r'pairs through $t=128$ and three at $t=256$.',
        'tab:coordinatetimes', 'rrrrrrr',
        r'$t$ & $q+a$ & $d$ & Old (ms) & $d$-vector (ms) & Packed (ms) & Old/packed', rows))
    control_cases = [('interior_links', 'Vertex links'),
                     ('interior_three_way', 'Three-way mixture'),
                     ('capped_meridian_links', 'Capped meridian')]
    groups = [
        ('Disc counts: old kernel / ray interface', 'discs', 'old_disc_A', 'ray_disc_A'),
        ('Coordinate censuses: old compact / packed', 'coordinates', 'old_compact_A', 'support_packed_A'),
        ('Fixed-trace transport: vector / packed', 'transport', 'transport_vector_A', 'transport_packed_A')]
    rows = []
    for number, (title, category, left, right) in enumerate(groups):
        if number:
            rows.append(r'\addlinespace[3pt]')
        rows.append(r'\multicolumn{4}{l}{\emph{' + title + r'}} \\')
        for key, label in control_cases:
            item = comparison(document, key + ':' + category, left, right)
            rows.append(' & '.join([label, ms(item['numerator_total_ns_median']),
                ms(item['denominator_total_ns_median']), ratio(item)]) + r' \\')
    parts.append(table(
        r'Control cases, five pairs per row. The first and second methods are named '
        r'in each group heading. Fixed-trace transport uses an identical selected basis '
        r'and independently checked orbit trace in both arms; its excluded setup contains '
        r'geometry, compilation, weight construction, and orbit discovery.',
        'tab:controls', 'lrrr', 'Case & First (ms) & Second (ms) & First/second', rows))
    rows = []
    for cohort in document['cohorts']:
        if cohort.get('category') != 'diagram_certificate_stage' or cohort['status'] != 'COMPLETE':
            continue
        selected = samples(document, cohort['id'], 'diagram_ray_A')
        crossings = int(cohort['case'].rsplit('_', 1)[1])
        rows.append(' & '.join([str(crossings), str(cohort['tetrahedra']), str(len(selected)),
            ms(median(document, cohort['id'], 'diagram_ray_A', 'generation_ns')),
            ms(median(document, cohort['id'], 'diagram_ray_A', 'external_verify_ns')),
            ms(median(document, cohort['id'], 'diagram_ray_A')),
            f"{selected[0]['certificate_json_bytes']:,}"]) + r' \\')
    parts.append(table(
        r'Source-bound certificates for stabilized-circle diagrams. The existing cocycle '
        r'discovers the supplied vector outside the timers. Generation includes two internal '
        r'disc replays, followed by a separately timed external source-bound replay. These '
        r'are new-wrapper A/A stages, not a comparison of complete automatic recognizers. '
        r'Separate stage medians need not sum to the total median.',
        'tab:diagramtimes', 'rrrrrrr',
        r'Crossings & $t$ & Calls & Generate (ms) & Verify (ms) & Total (ms) & Proof bytes', rows))
    (article_dir / 'generated_results.tex').write_text('\n'.join(parts) + '\n')


def export_plot_data(document, article_dir):
    rows = []
    for cohort in document['cohorts']:
        if cohort.get('family') != 'fibonacci' or cohort['status'] != 'COMPLETE':
            continue
        category = cohort['category']
        arms = {'discs': ('old_disc_A', 'ray_disc_A'),
                'coordinates': ('old_compact_A', 'support_packed_A'),
                'ray_capacity': ('ray_disc_A',)}.get(category, ())
        for arm in arms:
            selected = samples(document, cohort['id'], arm)
            for sample in selected:
                rows.append(dict(cohort=cohort['id'], category=category, arm=arm,
                    tetrahedra=cohort['tetrahedra'], statistic='raw', round=sample['round'],
                    measured_calls=len(selected), total_ns=sample['total_ns'],
                    total_ms=f"{sample['total_ns'] / 1e6:.9f}",
                    certificate_json_bytes=sample['certificate_json_bytes']))
            middle = statistics.median(sample['total_ns'] for sample in selected)
            rows.append(dict(cohort=cohort['id'], category=category, arm=arm,
                tetrahedra=cohort['tetrahedra'], statistic='median', round='',
                measured_calls=len(selected), total_ns=middle, total_ms=f'{middle / 1e6:.9f}',
                certificate_json_bytes=statistics.median(sample['certificate_json_bytes'] for sample in selected)))
    fields = ['cohort', 'category', 'arm', 'tetrahedra', 'statistic', 'round',
              'measured_calls', 'total_ns', 'total_ms', 'certificate_json_bytes']
    with (article_dir / 'benchmark_plot_data.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


def computed_summary(document, benchmark_path):
    controls = [row['paired_total_ratio_median'] for row in document['summaries']
                if row['control'] and row['reported']]
    fields = ('cohort', 'numerator_arm', 'denominator_arm', 'complete_pairs',
              'paired_total_ratio_median', 'paired_total_ratio_min', 'paired_total_ratio_max',
              'numerator_total_ns_median', 'denominator_total_ns_median')
    comparisons = [{key: row[key] for key in fields} for row in document['summaries']
                   if not row['control'] and row['reported']]
    return dict(schema='normal-support-rendered-summary-v1',
        benchmark_sha256=hashlib.sha256(benchmark_path.read_bytes()).hexdigest(),
        matplotlib_version=matplotlib.__version__, benchmark_status=document['status'],
        elapsed_seconds=document['elapsed_seconds'], sources_unchanged=document['sources_unchanged'],
        completed_cohorts=sum(row['status'] == 'COMPLETE' for row in document['cohorts']),
        measured_calls=sum(not row['warmup'] for row in document['samples']),
        warmup_calls=sum(row['warmup'] for row in document['samples']),
        incomplete_calls=sum(row['status'] != 'COMPLETE' for row in document['samples']),
        aa_median_ratio_range=[min(controls), max(controls)],
        exclusions=document.get('exclusions', []), comparisons=comparisons,
        plot_convention='actual A-arm calls and their separate medians; logarithmic axes; no fitted trends',
        audit_coverage='not computed here; use the independent audit artifact')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark', type=Path,
                        default=Path(__file__).with_name('results') / 'benchmark_20261009.json')
    parser.add_argument('--article-dir', type=Path, required=True)
    args = parser.parse_args()
    document = json.loads(args.benchmark.read_text())
    if document['status'] != 'COMPLETE' or not document['sources_unchanged']:
        raise ValueError('paper rendering requires a complete source-frozen benchmark')
    args.article_dir.mkdir(parents=True, exist_ok=True)
    render_figures(document, args.article_dir)
    render_tables(document, args.article_dir)
    export_plot_data(document, args.article_dir)
    (args.article_dir / 'computed_summary.json').write_text(
        json.dumps(computed_summary(document, args.benchmark), indent=2) + '\n')
    print('Rendered exact retained data into', args.article_dir.resolve())
    print('Figures: benchmarks.pdf/.png and proof_sizes.pdf/.png')
    print('Tables: generated_results.tex; data: benchmark_plot_data.csv; metadata: computed_summary.json')


if __name__ == '__main__':
    main()
