"""Regenerate the compact-coordinate table from complete paired measurements."""
import json
from pathlib import Path

DATA = Path(__file__).resolve().parent
report = json.loads((DATA/'compact-coordinates-benchmark.json').read_text())
lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrrr}', r'\toprule',
         r'Input & Dense ms & Compact ms & Dense/compact & Dense A/A & Compact A/A \\', r'\midrule']
for case in report['cases']:
    assert all(m['completed'] for s in case['samples']+case['warmups'] for m in s['measurements'].values())
    m, r = case['medians'], case['paired_ratios']
    lines.append(f"{case['source']['name']} & {1000*m['old']:.3f} & {1000*m['compact']:.3f} & "
                 f"{r['old/compact']:.3f} & {r['old/old_AA']:.3f} & {r['compact/compact_AA']:.3f} "+r'\\')
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
(DATA.parent/'tables/compact_coordinates.tex').write_text('\n'.join(lines)+'\n')
