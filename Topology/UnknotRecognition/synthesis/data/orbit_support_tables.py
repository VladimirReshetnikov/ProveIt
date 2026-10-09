"""Tables of complete orbit-query and recognition timings with A/A controls."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LABELS = {'optimized-positive': 'Optimized positive', 'trefoil': 'Trefoil',
          'five-cycle-16-bits-0': 'Five-cycle, small',
          'five-cycle-16-bits-4096': 'Five-cycle, 4096 bits'}
for mode in ('orbits', 'recognize'):
    data = json.loads((ROOT/f'data/orbit-support-{mode}.json').read_text())
    lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
    for row in data['cases']:
        label = LABELS.get(row['name'], row['name']).replace('_', r'\_')
        assert row['paired_ratios']['old_new']['count'] == 5
        ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
        lines.append(label + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                     + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}']
    (ROOT/f'tables/orbit_support_{mode}.tex').write_text('\n'.join(lines)+'\n')
