"""Tables derived from final power-pair capacity and recognition records."""
import json
from pathlib import Path

DATA=Path(__file__).resolve().parent;TABLES=DATA.parent/'tables'
audit=json.loads((DATA/'power-pair-audit.json').read_text())
lines=[r'\begin{center}\small',r'\begin{tabular}{rrrrr}',r'\toprule',
       r'Pairs $k$ & Power parameter $b$ & Source nodes & Production work & Replay work \\',r'\midrule']
for row in audit['capacity']:
    assert row['source_nodes']==row['final_nodes']
    lines.append(' & '.join(str(row[k]) for k in ('pairs','bits','source_nodes','production_work','replay_work'))+r' \\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(TABLES/'power_pair_capacity.tex').write_text('\n'.join(lines)+'\n')
data=json.loads((DATA/'power-pair-benchmark.json').read_text())
lines=[r'\begin{center}\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Case & Old ms & New ms & Old/new & Old A/A & New A/A \\',r'\midrule']
for row in data['cases']:
    assert all(m['completed'] for s in row['samples']+row['warmups'] for m in s['measurements'].values())
    name=row['source']['name'].replace('_',r'\_');med=row['medians'];ratios=row['paired_ratios']
    lines.append(f"{name} & {1000*med['old']:.3f} & {1000*med['current']:.3f} & "
                 f"{ratios['current']['median']:.3f} & {ratios['old_AA']['median']:.3f} & "
                 f"{ratios['current_AA']['median']:.3f} "+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(TABLES/'power_pair_benchmark.tex').write_text('\n'.join(lines)+'\n')
