"""Render paired complete-call measurements for sparse cocycle discovery."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LABELS = {'survivor-00': 'Survivor 00', 'gordian': 'Gordian',
          'optimized-positive': 'Optimized positive', 'genus-one-miss': 'Genus-one miss',
          'trefoil': 'Trefoil'}
for mode in ('prepare', 'recognize'):
    data = json.loads((ROOT/f'data/cocycle-sparse-{mode}.json').read_text())
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
    for row in data['cases']:
        label = LABELS.get(row['name'], row['name']).replace('_', r'\_')
        assert row['paired_ratios']['old_new']['count'] == 5
        ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
        lines.append(label + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                     + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/f'tables/cocycle_sparse_{mode}.tex').write_text('\n'.join(lines)+'\n')
