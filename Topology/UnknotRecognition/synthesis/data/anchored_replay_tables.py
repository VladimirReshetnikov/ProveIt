"""Regenerate source-anchored replay tables from complete paired calls."""
import json
from pathlib import Path
DATA = Path(__file__).resolve().parent
for mode in ('kernels', 'source', 'pipeline'):
    report = json.loads((DATA / f'anchored-replay-{mode}.json').read_text())
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrrr}', r'\toprule',
             r'Case & Old ms & New ms & Old/new & Old A/A & New A/A \\', r'\midrule']
    for case in report['cases']:
        assert all(m['completed'] for s in case['samples'] + case['warmups']
                   for m in s['measurements'].values())
        m, r = case['medians'], case['paired_ratios']
        ratios = ([r[k]['median'] for k in ('current', 'old_AA', 'current_AA')]
                  if mode == 'pipeline' else
                  [r[k] for k in ('old/current', 'old/old_AA', 'current/current_AA')])
        name = case['source']['name'].replace('_', r'\_')
        lines.append(f'{name} & {1000*m["old"]:.3f} & {1000*m["current"]:.3f} & '
                     + ' & '.join(f'{x:.3f}' for x in ratios) + r' \\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    (DATA.parent / f'tables/anchored_replay_{mode}.tex').write_text('\n'.join(lines) + '\n')
