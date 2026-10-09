"""Paired complete recognizer timings for alternative tree gauges."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT/'data/cocycle-trees-recognize.json').read_text())
labels = {'raw-circle': 'Raw circle', 'optimized-positive': 'Optimized positive',
          'early-two': 'Early trial 2', 'early-three': 'Early trial 3',
          'early-five': 'Five-crossing early', 'late-24': 'Late, 24-trial option',
          'genus-one-miss': 'Genus-one miss', 'trefoil': 'Trefoil'}
lines = [r'\begin{tabular}{lrrrrr}', r'\toprule',
         r'Input & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\', r'\midrule']
for row in data['cases']:
    assert row['paired_ratios']['old_new']['count'] == 9
    ratios = [row['paired_ratios'][key]['median'] for key in ('old_new', 'old_AA', 'new_AA')]
    lines.append(labels[row['name']] + f" & {1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                 + ' & '.join(f'{v:.3f}' for v in ratios) + r' \\')
lines += [r'\bottomrule', r'\end{tabular}']
(ROOT/'tables/cocycle_trees_recognize.tex').write_text('\n'.join(lines)+'\n')
