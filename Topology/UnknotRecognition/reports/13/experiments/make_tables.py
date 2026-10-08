"""Regenerate TeX tables directly from the bundled raw benchmark JSON."""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'paper' / 'tables'
OUT.mkdir(parents=True, exist_ok=True)

NAMES = {'conway': 'Conway', 'kinoshita_terasaka': 'Kinoshita--Terasaka',
         'hard_unknot_8': 'Hard unknot', 'grid_determinant_one_knot': 'Determinant-one grid',
         'stress_braid5_36': 'Mixed 5-braid', 'conway_mirrored_h0': 'Conway, mirrored',
         'kinoshita_terasaka_mirrored_h0': 'K--T, mirrored',
         'torus_4_7_filter_control': '$T(4,7)$ control',
         'torus_2_31_peak_control': '$T(2,31)$ control',
         'torus_3_7': '$T(3,7)$', 'torus_4_7': '$T(4,7)$'}


def table(filename, columns, headers, rows, caption, label):
    body = ['\\begin{table}[htbp]', '\\centering\\small',
            '\\setlength{\\tabcolsep}{4pt}', '\\begin{tabular}{' + columns + '}',
            '\\toprule', ' & '.join(headers) + r' \\', '\\midrule']
    body += [' & '.join(map(str, row)) + r' \\' for row in rows]
    body += ['\\bottomrule', '\\end{tabular}', '\\caption{' + caption + '}',
             '\\label{' + label + '}', '\\end{table}', '']
    (OUT / filename).write_text('\n'.join(body))


def main():
    window = json.loads((ROOT / 'results/window_benchmark.json').read_text())
    rows, peaks = [], []
    for c in window['cases']:
        full, part = c['full']['median_seconds'], c['window']['median_seconds']
        rows.append([NAMES[c['name']], c['crossings'], f'{1000*full:.3f}',
                     f'{1000*part:.3f}', f'{full/part:.3f}', c['window_rank']])
        peaks.append([NAMES[c['name']],
                      format(c['full']['stats']['max_objects_before_elimination'], ','),
                      format(c['window']['stats']['max_objects_before_elimination'], ','),
                      'Yes' if c['is_nontriviality_certificate'] else 'No'])
    table('window_timings.tex', 'lrrrrr',
          ['Input', '$n$', 'Full (ms)', 'Window (ms)', 'Full/window', '$\\dim H^0$'],
          rows, 'Scanner-kernel medians from seven alternating pairs after a warmup of each '
          'variant. The window computes only normalized degree zero, while the full scan '
          'computes every degree. Input preparation and order selection are excluded.', 'tab:window-times')
    table('window_allocations.tex', 'lrrc', ['Input', 'Full peak', 'Window peak', 'Window rejects unknot?'],
          peaks, 'Peak physical objects allocated before elimination. These are object counts, '
          'not peak resident-memory measurements. A degree-zero dimension of two is inconclusive.',
          'tab:window-objects')
    perturb = json.loads((ROOT / 'results/perturbation_benchmarks.json').read_text())
    natural, synthetic = [], []
    for r in perturb['rows']:
        old, new = r['median_seconds']
        suffix = [f'{1000*old:.3f}', f'{1000*new:.3f}', f'{old/new:.3f}']
        if r['kind'] == 'knot_scan':
            natural.append([NAMES[r['case']], r['crossings']] + suffix)
        else:
            synthetic.append([r['matrix_order'], r['input_objects']] + suffix)
    table('perturbation_natural.tex', 'lrrrr', ['Input', '$n$', 'Scalar (ms)', 'Perturbation (ms)', 'Scalar/pert.'],
          natural, 'Full Khovanov scans: five warmed alternating pairs, fixed order, shape cache '
          'disabled in both backends. The perturbation backend is slower on every natural input tested.',
          'tab:hpl-natural')
    table('perturbation_synthetic.tex', 'rrrrr', ['$R$ order', 'Objects', 'Scalar (ms)', 'Perturbation (ms)', 'Scalar/pert.'],
          synthetic, 'Synthetic two-term complexes with differential $I+xR$ over '
          '$\\mathbb F_2[x]/(x^2)$. These are algebraic stress tests, not knot diagrams. '
          'Both timings include construction of the same input complex.', 'tab:hpl-synthetic')
    h = json.loads((ROOT / 'hierarchy/benchmark_results.json').read_text())
    terminal = [[r['darts'], f"{1000*r['fast']['median_seconds']:.3f}",
                 f"{1000*r['report06']['median_seconds']:.3f}", f"{r['median_speedup']:.1f}"]
                for r in h['comparison']]
    table('terminal_timings.tex', 'rrrr', ['Darts', 'New (ms)', 'Report 06 (ms)', 'Old/new'], terminal,
          'Known-ball terminal classifier: medians of three complete calls including validation. '
          'The fixture family is dual to bipyramid triangulations. No complete hierarchy is timed.',
          'tab:terminal-times')
    scaling = [[r['darts'], f"{1000*r['fast']['median_seconds']:.3f}",
                r['fast']['candidate_pairs']] for r in h['fast_scaling']]
    table('terminal_scaling.tex', 'rrr', ['Darts', 'New (ms)', 'Candidate pairs'], scaling,
          'Larger essential terminal fixtures, without running the quartic baseline. '
          'Counts and individual timings are in the raw JSON.', 'tab:terminal-scaling')
    print('Regenerated six TeX tables from bundled benchmark JSON')


if __name__ == '__main__':
    main()
