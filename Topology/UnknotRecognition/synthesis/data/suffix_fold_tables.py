"""Regenerate the suffix-fold comparison table from complete paired calls."""
import json
from pathlib import Path
DATA=Path(__file__).resolve().parent
report=json.loads((DATA/'suffix-fold-benchmark.json').read_text())
lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Query & Old ms & New ms & Old/new & Old A/A & New A/A \\',r'\midrule']
for case in report['cases']:
    assert all(m['completed'] for s in case['samples']+case['warmups'] for m in s['measurements'].values())
    m,r=case['medians'],case['paired_ratios']
    lines.append(f"{case['source']['name']} & {1000*m['old']:.3f} & {1000*m['current']:.3f} & "
                 f"{r['old/current']:.3f} & {r['old/old_AA']:.3f} & {r['current/current_AA']:.3f} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(DATA.parent/'tables/suffix_folds.tex').write_text('\n'.join(lines)+'\n')
