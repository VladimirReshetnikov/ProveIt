"""Tables retain complete enumeration and proof-replayed discovery scopes."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'data/planar-sectors-benchmark.json').read_text())
for group in ('enumeration','discovery'):
    lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
        r'Input & old ms & new ms & old/new & old A/A & new A/A\\',r'\midrule']
    for row in data['cases']:
        kind,name=row['name'].split('/')
        if kind!=group:continue
        if name=='empty-sector':label='Empty sector'
        else:
            cap,_,n=name.split('-');label=f'Base {n}, '+('two caps' if cap=='double' else 'one cap')
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['output_sha256']==values[0]['output_sha256']for v in values)
        cells=[label]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
        cells += [f"{row['paired_ratios'][a]['median']:.3f}"for a in ('old_new','old_AA','new_AA')]
        lines.append(' & '.join(cells)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
    (ROOT/'tables'/f'planar_sectors_{group}.tex').write_text('\n'.join(lines)+'\n')

lex=json.loads((ROOT/'data/lex-benchmark.json').read_text())
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrr}',r'\toprule',
    r'Complete recognition & default ms & enabled ms & default/enabled\\',r'\midrule']
for row in lex['cases']:
    if not row['name'].startswith('recognition/'):continue
    cells=[row['name'].split('/')[1].replace('-',' ')]+[f"{1000*row['medians'][a]:.3f}"for a in ('old','new')]
    cells.append(f"{row['paired_ratios']['old_new']['median']:.3f}")
    lines.append(' & '.join(cells)+r'\\')
lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
(ROOT/'tables/cocycle_lex_recognition.tex').write_text('\n'.join(lines)+'\n')
