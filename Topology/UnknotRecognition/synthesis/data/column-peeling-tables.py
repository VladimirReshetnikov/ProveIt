"""Regenerate the compact timing table from the retained paired samples."""
import json
from pathlib import Path
HERE=Path(__file__).parent
report=json.loads((HERE/'column-peeling-benchmark.json').read_text())
assert report['finished']
labels={
 'prepared-106-core-production':'106 prepared cores: produce',
 'prepared-common-core-replay':'90 prepared cores: replay',
 'pilot/lst_4_7/0':'LST(4,7): complete query',
 'fibonacci_lst_09/mixed':'Fibonacci 9 mixed: complete query',
 'pilot/fibonacci_lst_07/0':'Fibonacci 7 pilot: v4 to v5',
 'pilot/fibonacci_lst_09/0':'Fibonacci 9 pilot: v4 to v5',
 'pilot/fibonacci_lst_04/0':'Fibonacci 4 pilot: refusal',
 'pilot/fibonacci_lst_10/0':'Fibonacci 10 pilot: refusal',
}
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrr}',r'\toprule',
       r'Case & Old (ms) & New (ms) & Paired gain & A/A \\',r'\midrule']
for row in report['cases']:
    key=row['label']
    if key.startswith('matrix-chain-'):label='Matrix chain '+key.rsplit('-',1)[-1]
    elif key.startswith('conditional-replay-chain-'):label='Conditional replay '+key.rsplit('-',1)[-1]
    else:label=labels[key]
    lines.append(f"{label} & {row['old_median']*1000:.3f} & {row['new_median']*1000:.3f} & {row['paired_speedup']:.3f} & {row['aa_median']:.3f}"+r' \\')
lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(HERE.parent/'tables/column_peeling_timing.tex').write_text('\n'.join(lines)+'\n')
