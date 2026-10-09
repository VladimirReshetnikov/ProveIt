"""Format completed cocycle and recognition calls with both A/A controls."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LABELS = {'circle-1-bits-0': '1 crossing', 'circle-4-bits-0': '4 crossings',
          'circle-8-bits-0': '8 crossings', 'circle-16-bits-0': '16 crossings',
          'circle-4-bits-4096': '4 crossings, 4096 bits',
          'raw-circle': 'Raw circle', 'optimized-positive': 'Optimized positive',
          'genus-one-miss': 'Genus-one miss', 'trefoil': 'Trefoil', 'figure-eight': 'Figure-eight'}
for mode in ('optimize', 'source', 'pipeline'):
    data = json.loads((ROOT/f'data/cocycle-seed-{mode}.json').read_text())
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
    for row in data['cases']:
        label = LABELS.get(row['name'], row['name']).replace('_', r'\_')
        assert row['paired_ratios']['old_new']['count'] == 5
        ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
        lines.append(label + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                     + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/f'tables/cocycle_seed_{mode}.tex').write_text('\n'.join(lines)+'\n')
