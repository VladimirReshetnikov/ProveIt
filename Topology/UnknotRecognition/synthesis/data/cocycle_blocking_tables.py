"""Complete-call tables for adaptive zero-cost cocycle blocking flows."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
labels = {'equal-32': 'Equal cost, 32 rows', 'equal-128': 'Equal cost, 128 rows',
          'equal-512': 'Equal cost, 512 rows', 'distinct-128': 'Distinct costs, 128 rows',
          'random-suite': '24 random 24-row queries', 'circle-32': 'Circle, 32 crossings',
          'circle-4-binary': 'Circle, 4 crossings, binary', 'raw-circle': 'Raw circle',
          'optimized-positive': 'Optimized positive', 'early-two': 'Early tree positive',
          'late-24': 'Late tree positive', 'genus-one-miss': 'Genus-one miss', 'trefoil': 'Trefoil'}
for mode in ('optimize', 'recognize'):
    data = json.loads((ROOT/f'data/cocycle-blocking-{mode}.json').read_text())
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
    for row in data['cases']:
        assert row['paired_ratios']['old_new']['count'] == 5
        ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
        lines.append(labels[row['name']] + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                     + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/f'tables/cocycle_blocking_{mode}.tex').write_text('\n'.join(lines)+'\n')
