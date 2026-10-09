"""Regenerate the isolated shelling-recognition timing table."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/boundary-shellings-recognize-final.json').read_text())
rows=[r'\begin{tabular}{lrrrrr}',r'\toprule',
      r'Source & Off ms & On ms & Off/on & Off A/A & On A/A \\',r'\midrule']
for case in r['cases']:
    m=case['medians'];p=case['paired_ratios']
    rows.append(f"{case['name']} & {1000*m['old']:.3f} & {1000*m['new']:.3f} & {p['old_new']['median']:.3f} & {p['old_AA']['median']:.3f} & {p['new_AA']['median']:.3f}"+r' \\')
rows.extend([r'\bottomrule',r'\end{tabular}'])
(ROOT/'tables/boundary_shellings_recognize.tex').write_text('\n'.join(rows)+'\n')
