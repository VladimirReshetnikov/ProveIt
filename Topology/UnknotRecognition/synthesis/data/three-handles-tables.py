"""Regenerate the three-handle complete-query timing table."""
import json
from pathlib import Path
HERE=Path(__file__).parent
report=json.loads((HERE/'three-handles-benchmark.json').read_text());assert report['finished']
labels={'pilot/interior_1_2/0':'Interior (1,2) pilot','pilot/interior_2_3/0':'Interior (2,3) pilot',
        'pilot/interior_3_5/0':'Interior (3,5) pilot','pilot/finite_trefoil_interior/0':'Interior trefoil pilot',
        'interior_1_2/mixed':'Interior (1,2) mixed','interior_3_5/mixed':'Interior (3,5) mixed',
        'finite_figureEight_interior/mixed':'Interior figure-eight mixed'}
lines=[r'\begin{center}',r'\small',r'\begin{tabular}{lrrrrr}',r'\toprule',
       r'Case & Copies & Native (ms) & Explicit (ms) & Ratio & A/A \\',r'\midrule']
for r in report['cases']:
    lines.append(f"{labels[r['source']]} & {r['copies']} & {1000*r['native_median']:.3f} & {1000*r['explicit_median']:.3f} & {r['paired_speedup']:.3f} & {r['aa_median']:.3f}"+r' \\')
lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(HERE.parent/'tables/three_handles_timing.tex').write_text('\n'.join(lines)+'\n')
