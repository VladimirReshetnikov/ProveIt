"""Complete first-descent source and actual diagram query measurements."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
for datafile,group,target in (('cover-oracle-source-benchmark.json',None,'sources'),
    ('cover-oracle-diagram-benchmark.json','native','queries'),
    ('cover-oracle-diagram-benchmark.json','recognition','recognition')):
    data=json.loads((ROOT/'data'/datafile).read_text())
    lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Input & previous ms & current ms & old/new & old A/A & new A/A\\',r'\midrule']
    for row in data['cases']:
        if group is not None:
            kind,name=row['name'].split('/')
            if kind!=group:continue
        else:name=row['name']
        cells=[name.replace('-',' ')]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
        cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'cover_oracle_{target}.tex').write_text('\n'.join(lines)+'\n')
