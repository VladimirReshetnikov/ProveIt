"""Tables for complete weighted queries and native-stage recognitions."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LABELS = {'connected-3': 'Connected, 3 weights', 'connected-128': 'Connected, 128 weights',
          'connected-128-binary': '128 weights, 4096 bits', 'disconnected-control': 'Disconnected control',
          'optimized-positive': 'Optimized positive', 'trefoil': 'Trefoil'}
for mode in ('weighted', 'recognize'):
    data = json.loads((ROOT/f'data/single-orbit-{mode}.json').read_text())
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
    for row in data['cases']:
        label = LABELS.get(row['name'], row['name']).replace('_', r'\_')
        assert row['paired_ratios']['old_new']['count'] == 5
        ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
        lines.append(label + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                     + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/f'tables/single_orbit_{mode}.tex').write_text('\n'.join(lines)+'\n')
