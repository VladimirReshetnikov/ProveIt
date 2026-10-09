"""Complete source-exterior construction/check timings, with A/A controls."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'data/diagram-exterior-benchmark.json').read_text())
lines = [r'\begin{tabular}{rrrrrrr}', r'\toprule',
         r'Crossings & New tets & Old (ms) & New (ms) & Old/new & Old A/A & New A/A \\',
         r'\midrule']
for row in data['cases']:
    lines.append(f"{row['crossings']} & {row['warmup']['new']['tetrahedra']} & "
                 f"{1000*row['medians']['old']:.3f} & {1000*row['medians']['new']:.3f} & "
                 f"{row['paired_old_new']:.3f} & {row['paired_old_AA']:.3f} & "
                 f"{row['paired_new_AA']:.3f} " + r'\\')
lines += [r'\bottomrule', r'\end{tabular}']
(ROOT / 'tables/diagram_exterior.tex').write_text('\n'.join(lines) + '\n')
