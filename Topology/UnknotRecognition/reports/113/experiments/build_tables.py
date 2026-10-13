#!/usr/bin/env python3
"""Build article tables from frozen evidence, without running experiments."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
e=ROOT/'evidence';a=ROOT/'article'
m=json.loads((e/'mode_benchmark.json').read_text());n=json.loads((e/'normal_benchmark.json').read_text())
lines=[r'\begin{tabular}{@{}rrrrrr@{}}',r'\toprule',
       r'Blocks & Histories & Cartesian & Atlas total & Reused query & Total ratio\\',r'\midrule']
for row in m['rows']:
 t=row['median_ms'];lines.append(f"{row['blocks']} & {row['global_mode_histories']:,} & {t['cartesian']:.4f} & {t['atlas_prepare_query']:.4f} & {t['atlas_query']:.4f} & {row['full_kernel_ratio']:.3f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(a/'mode_table.tex').write_text('\n'.join(lines)+'\n')
(a/'measured.tex').write_text(
 f"\\newcommand{{\\NormalBase}}{{{n['median_ms']['unsplit']:.3f}}}\n"
 f"\\newcommand{{\\NormalSplit}}{{{n['median_ms']['split']:.3f}}}\n"
 f"\\newcommand{{\\NormalRatio}}{{{n['ratio']:.2f}}}\n"
 f"\\newcommand{{\\ModeRatio}}{{{m['rows'][-1]['full_kernel_ratio']:.2f}}}\n")
print('Frozen evidence tables written.')
