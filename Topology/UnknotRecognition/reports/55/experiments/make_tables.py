import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'results'/'benchmark.json').read_text())
labels={'tiny':'Tiny','static_256':'Static','reflection_512':'Reflection'}
lines=[r'\begin{table}[htbp]',r'\centering\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Fixture & $D$ & Dense (ms) & Sparse (ms) & Selective (ms) & Sparse/sel.\\',r'\midrule']
for row in r['summaries']:
    name=row['name'];label=labels.get(name)
    if label is None:
        label='Dense profiles' if name.startswith('dense_profiles') else name.split('_')[0].capitalize()
    m=row['median_seconds'];ratio=row['paired_ratio_to_selective']['sparse']
    lines.append(f"{label} & {row['dimension']} & {1000*m['dense']:.3f} & {1000*m['sparse']:.3f} & {1000*m['selective']:.3f} & {ratio:.3f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}',r'\caption{Cold supplied-interval queries. Times are per-arm medians; the last column is the median paired sparse/selective ratio, so values above one favour selective extraction. Discovery, native geometry and terminal disc verification are excluded. All completed results, including losses, are retained.}',r'\label{tab:timings}',r'\end{table}'])
(root/'article'/'results_table.tex').write_text('\n'.join(lines)+'\n')
